//! A toy chain for BAT fee tokens: the state a pallet would keep (escrow, issued/spent/refunded
//! counters, sessions, nullifiers) and the checks it would run. Escrow and client payments are
//! locked in one pool account and spends and refunds are paid out of it.
//!
//! Messages and the checks on them come from the BAT wrapper in `polymesh-dart`, which fixes the
//! curves.

use std::collections::{BTreeMap, BTreeSet};

use polymesh_bat::{protocol, signature::BatchSig};
use polymesh_dart::{
    bat_signature_base, BatClientSession, BatFeePayment, BatIssueRequest, BatIssueResponse,
    BatIssuerKeyId, BatIssuerKeys, BatIssuerPublicKey, BatIssuerSession, BatNullifier,
    BatOnChainIssuanceRequest, BatPairing, BatPreToken, BatRefundKey, BatRefundRequest, BatReveal,
    BatSessionId, PallasA,
};
use rand_chacha::ChaCha20Rng;
use rand_core::{CryptoRng, RngCore, SeedableRng};

type RefundRequest = protocol::RefundRequest<BatPairing, PallasA>;

pub type Amount = u64;
/// Number of blocks. Used to represent time.
pub type Block = u32;
pub type IssuerId = u32;
/// Index of an issuer key. Each key has one denomination.
pub type KeyId = BatIssuerKeyId;
pub type Sid = BatSessionId;

/// Holds escrow and client payments. Spends and refunds are paid out of it.
pub const POOL: &str = "pool";
/// Receives fees paid with tokens, and client payments for tokens neither spent nor refunded by
/// retirement.
pub const TREASURY: &str = "treasury";

/// Locking `native` gives a token worth `bat`.
#[derive(Clone, Copy, Debug)]
pub struct Rate {
    /// This would be POLYX
    pub native: Amount,
    pub bat: Amount,
}

#[derive(Clone, Debug)]
pub struct SystemParams {
    /// Escrow must be at least `escrow_factor / 100` times the value of tokens issued under an
    /// issuer, so 150 means 1.5. The same bound caps the value spent under it. At least 100.
    pub escrow_factor: u32,
    /// The minimum duration between issuer registration and retirement.
    pub t_ret: Block,
    /// Time before retirement issuance must be paused.
    pub t_grace: Block,
    /// Delay after which pending "buy"s expire.
    pub expiry_delay: Block,
    /// The smallest denomination.
    pub base_rate: Rate,
    /// Denominations as multiples of `base_rate`. An issuer registers one key for each.
    pub multipliers: Vec<Amount>,
}

impl Default for SystemParams {
    fn default() -> Self {
        Self {
            escrow_factor: 200,
            t_ret: 100,
            t_grace: 10,
            expiry_delay: 5,
            base_rate: Rate { native: 1, bat: 1 },
            multipliers: vec![1],
        }
    }
}

pub struct IssuerAccount {
    pub owner: String,
    /// One per entry of `multipliers`.
    pub keys: Vec<KeyId>,
    /// Total escrow amount
    pub esc: Amount,
    /// Escrow plus client payments, less what spends and refunds paid out. Held by `POOL`.
    pub locked: Amount,
    /// Percent of a session's value the client pays the issuer when it posts `k`.
    pub commission_percent: u32,
    pub retire_at: Block,
    pub retired: bool,
}

impl IssuerAccount {
    /// Value of tokens that can be issued, and spent, against the escrow.
    fn cap(&self, escrow_factor_percent: u32) -> Amount {
        (self.esc as u128 * 100 / escrow_factor_percent as u128) as Amount
    }
}

pub struct IssuerPerKeyTracking {
    pub issuer: IssuerId,
    pub pk_iss: BatIssuerPublicKey,
    /// Worth of a token in BAT.
    pub denom: Amount,
    /// Native amount locked per token.
    pub value: Amount,
    pub n_iss: Amount,
    pub n_spent: Amount,
    pub n_ref: Amount,
}

pub enum SessionState {
    AwaitingIssuer { expires: Block },
    Issued { reveal: BatReveal, refunded: bool },
    Reclaimed,
}

pub struct Session {
    pub payer: String,
    /// Names the key, `pk_ref`, `com_k` and the number of tokens.
    pub request: BatOnChainIssuanceRequest,
    /// Held with the payment, paid to the issuer when it posts `k`.
    pub commission: Amount,
    pub state: SessionState,
}

pub struct Payment {
    pub payment: BatFeePayment,
    pub ad: Vec<u8>,
}

pub struct Chain {
    pub params: SystemParams,
    pub height: Block,
    pub balances: BTreeMap<String, Amount>,
    pub issuers: Vec<IssuerAccount>,
    pub keys: Vec<IssuerPerKeyTracking>,
    pub sessions: BTreeMap<Sid, Session>,
    pub nullifiers: BTreeSet<BatNullifier>,
    /// Client payments and commissions in `POOL` waiting for the issuer to post `k`.
    pub held: Amount,
    genesis: Amount,
    rng: ChaCha20Rng,
}

impl Chain {
    pub fn new(params: SystemParams, balances: &[(&str, Amount)]) -> Self {
        // Below 1 the cap exceeds the escrow, so spends and refunds could draw on other issuers'
        // share of the pool.
        assert!(params.escrow_factor >= 100, "escrow_factor below 1");
        assert!(
            params.base_rate.native > 0
                && params.base_rate.bat > 0
                && !params.multipliers.is_empty()
                && !params.multipliers.contains(&0),
            "zero denomination"
        );
        Self {
            params,
            height: 0,
            balances: balances.iter().map(|(a, b)| (a.to_string(), *b)).collect(),
            issuers: Vec::new(),
            keys: Vec::new(),
            sessions: BTreeMap::new(),
            nullifiers: BTreeSet::new(),
            held: 0,
            genesis: balances.iter().map(|(_, b)| b).sum(),
            rng: ChaCha20Rng::seed_from_u64(1),
        }
    }

    pub fn advance_to(&mut self, height: Block) {
        self.height = self.height.max(height);
    }

    /// Applies to issuers registered afterwards. Registered keys keep their denomination and value.
    pub fn set_base_rate(&mut self, rate: Rate) -> Result<(), Error> {
        if rate.native == 0 || rate.bat == 0 {
            return Err(Error::BadRate);
        }
        self.params.base_rate = rate;
        Ok(())
    }

    /// One key per denomination. Escrow is locked until the issuer retires, which it can't do
    /// before `t_ret` blocks.
    pub fn register_issuer(
        &mut self,
        owner: &str,
        pk_iss: &[BatIssuerPublicKey],
        esc: Amount,
        commission_percent: u32,
    ) -> Result<IssuerId, Error> {
        if pk_iss.len() != self.params.multipliers.len()
            || pk_iss.iter().any(|pk| pk.validate().is_err())
        {
            return Err(Error::BadKey);
        }
        // Escrow money into the pool
        self.transfer(owner, POOL, esc)?;
        let id = self.issuers.len() as IssuerId;
        let rate = self.params.base_rate;
        let first = self.keys.len() as KeyId;
        for (pk, m) in pk_iss.iter().zip(&self.params.multipliers) {
            self.keys.push(IssuerPerKeyTracking {
                issuer: id,
                pk_iss: *pk,
                denom: m * rate.bat,
                value: m * rate.native,
                n_iss: 0,
                n_spent: 0,
                n_ref: 0,
            });
        }
        self.issuers.push(IssuerAccount {
            owner: owner.into(),
            keys: (first..self.keys.len() as KeyId).collect(),
            esc,
            locked: esc,
            commission_percent,
            retire_at: self.height + self.params.t_ret,
            retired: false,
        });
        Ok(id)
    }

    /// Locks more escrow behind an existing issuer, which raises its cap.
    pub fn top_up_escrow(
        &mut self,
        who: &str,
        issuer: IssuerId,
        amount: Amount,
    ) -> Result<(), Error> {
        let acc = self
            .issuers
            .get(issuer as usize)
            .ok_or(Error::UnknownIssuer)?;
        if acc.owner != who {
            return Err(Error::NotAllowed);
        }
        if acc.retired {
            return Err(Error::Retired);
        }
        self.transfer(who, POOL, amount)?;
        let acc = &mut self.issuers[issuer as usize];
        acc.esc += amount;
        acc.locked += amount;
        Ok(())
    }

    /// Client's half of Π-Execute. Its payment and the issuer's commission are held in the pool
    /// until the issuer posts `k`.
    pub fn issue_for_client(
        &mut self,
        payer: &str,
        request: &BatOnChainIssuanceRequest,
    ) -> Result<(), Error> {
        request.verify::<()>().map_err(|_| Error::Malformed)?;
        let k = self
            .keys
            .get(request.issuer as usize)
            .ok_or(Error::UnknownIssuer)?;
        let acc = &self.issuers[k.issuer as usize];
        if acc.retired {
            return Err(Error::Retired);
        }
        if self.sessions.contains_key(&request.sid) {
            return Err(Error::SessionExists);
        }
        let paid = request.count as Amount * k.value;
        let commission = (paid * acc.commission_percent as Amount).div_ceil(100);
        self.transfer(payer, POOL, paid + commission)?;
        self.held += paid + commission;
        self.sessions.insert(
            request.sid,
            Session {
                payer: payer.into(),
                request: *request,
                commission,
                state: SessionState::AwaitingIssuer {
                    expires: self.height + self.params.expiry_delay,
                },
            },
        );
        Ok(())
    }

    /// Issuer's half. The client's payment stays locked in the pool and the commission goes to the
    /// issuer.
    pub fn issue_for_issuer(&mut self, who: &str, reveal: &BatReveal) -> Result<(), Error> {
        let s = self
            .sessions
            .get(&reveal.sid)
            .ok_or(Error::UnknownSession)?;
        let SessionState::AwaitingIssuer { .. } = s.state else {
            return Err(Error::NotAwaitingIssuer);
        };
        let key_id = s.request.issuer;
        let key = &self.keys[key_id as usize];
        let issuer = key.issuer;
        let acc = &self.issuers[issuer as usize];
        if acc.owner != who {
            return Err(Error::NotAllowed);
        }
        if acc.retired {
            return Err(Error::Retired);
        }
        if self.height + self.params.t_grace > acc.retire_at {
            return Err(Error::IssuanceFrozen);
        }
        let (l, commission) = (s.request.count as Amount, s.commission);
        let paid = l * key.value;
        if self.value_of(issuer, |k| k.n_iss) + paid > acc.cap(self.params.escrow_factor) {
            return Err(Error::OverCapacity);
        }
        if reveal
            .verify(&key.pk_iss, &s.request.commitment_to_sig_mask)
            .is_err()
        {
            return Err(Error::WrongK);
        }

        let owner = acc.owner.clone();
        self.transfer(POOL, &owner, commission)?;
        self.held -= paid + commission;
        self.issuers[issuer as usize].locked += paid;
        self.keys[key_id as usize].n_iss += l;
        self.sessions.get_mut(&reveal.sid).unwrap().state = SessionState::Issued {
            reveal: reveal.clone(),
            refunded: false,
        };
        Ok(())
    }

    /// Client takes its payment and the commission back if the issuer never posted `k`.
    pub fn reclaim(&mut self, who: &str, sid: Sid) -> Result<(), Error> {
        let s = self.sessions.get(&sid).ok_or(Error::UnknownSession)?;
        let SessionState::AwaitingIssuer { expires } = s.state else {
            return Err(Error::NotAwaitingIssuer);
        };
        if s.payer != who {
            return Err(Error::NotAllowed);
        }
        if self.height < expires {
            return Err(Error::TooEarly);
        }
        let paid =
            s.request.count as Amount * self.keys[s.request.issuer as usize].value + s.commission;
        self.transfer(POOL, who, paid)?;
        self.held -= paid;
        self.sessions.get_mut(&sid).unwrap().state = SessionState::Reclaimed;
        Ok(())
    }

    /// Pays a fee with tokens, possibly under several denomination keys, by unlocking their value
    /// from the pool to `TREASURY`.
    pub fn spend(&mut self, p: &Payment) -> Result<Amount, Error> {
        if p.payment.tokens.is_empty() {
            return Err(Error::Malformed);
        }
        let mut count = BTreeMap::<KeyId, Amount>::new();
        for (k, _) in p.payment.tokens.iter() {
            let key = self.keys.get(*k as usize).ok_or(Error::UnknownIssuer)?;
            if self.issuers[key.issuer as usize].retired {
                return Err(Error::Retired);
            }
            *count.entry(*k).or_default() += 1;
        }
        let nullifiers = p
            .payment
            .tokens
            .iter()
            .map(|(_, t)| t.pk_e)
            .collect::<Vec<_>>();
        if !distinct(&nullifiers) {
            return Err(Error::DuplicateToken);
        }
        if nullifiers.iter().any(|n| self.nullifiers.contains(n)) {
            return Err(Error::AlreadySpent);
        }
        let mut value = BTreeMap::<IssuerId, Amount>::new();
        for (&k, &n) in &count {
            let key = &self.keys[k as usize];
            *value.entry(key.issuer).or_default() += n * key.value;
        }
        for (&i, &v) in &value {
            let acc = &self.issuers[i as usize];
            if self.value_of(i, |k| k.n_spent) + v > acc.cap(self.params.escrow_factor) {
                return Err(Error::OverCapacity);
            }
            if acc.locked < v {
                return Err(Error::Insolvent);
            }
        }
        let pk_iss = count
            .keys()
            .map(|&k| (k, self.keys[k as usize].pk_iss))
            .collect::<BTreeMap<_, _>>();
        if p.payment.verify(&mut self.rng, &p.ad, &pk_iss).is_err() {
            return Err(Error::BadSignature);
        }

        let total = value.values().sum();
        self.transfer(POOL, TREASURY, total)?;
        for (&k, &n) in &count {
            self.keys[k as usize].n_spent += n;
        }
        for (&i, &v) in &value {
            self.issuers[i as usize].locked -= v;
        }
        self.nullifiers.extend(nullifiers);
        Ok(total)
    }

    /// Once per session, for tokens that were never spent. Unlocks their value from the pool to the
    /// payer. Tokens are checked against the key the session was bought under.
    pub fn refund(&mut self, req: &BatRefundRequest) -> Result<Amount, Error> {
        let s = self.sessions.get(&req.sid).ok_or(Error::UnknownSession)?;
        match s.state {
            SessionState::Issued {
                refunded: false, ..
            } => {}
            SessionState::Issued { refunded: true, .. } => return Err(Error::AlreadyRefunded),
            _ => return Err(Error::NotIssued),
        }
        let key_id = s.request.issuer;
        let key = &self.keys[key_id as usize];
        let issuer = key.issuer;
        let acc = &self.issuers[issuer as usize];
        if acc.retired {
            return Err(Error::Retired);
        }

        if req.tokens.len() as Amount > s.request.count as Amount {
            return Err(Error::Malformed);
        }
        let nullifiers = req.tokens.iter().map(|t| t.pk_e).collect::<Vec<_>>();
        if !distinct(&nullifiers) {
            return Err(Error::DuplicateToken);
        }
        if nullifiers.iter().any(|n| self.nullifiers.contains(n)) {
            return Err(Error::AlreadySpent);
        }
        let n = req.tokens.len() as Amount;
        let value = n * key.value;
        if acc.locked < value {
            return Err(Error::Insolvent);
        }
        if req
            .verify(&mut self.rng, &key.pk_iss, &s.request.pk_ref)
            .is_err()
        {
            return Err(Error::BadSignature);
        }

        let payer = s.payer.clone();
        self.transfer(POOL, &payer, value)?;
        self.keys[key_id as usize].n_ref += n;
        self.issuers[issuer as usize].locked -= value;
        self.nullifiers.extend(nullifiers);
        if let SessionState::Issued { refunded, .. } =
            &mut self.sessions.get_mut(&req.sid).unwrap().state
        {
            *refunded = true;
        }
        Ok(value)
    }

    /// Returns the escrow, less what spends and refunds took beyond the client payments, to the
    /// owner. Client payments for tokens neither spent nor refunded go to `TREASURY`.
    pub fn retire(&mut self, who: &str, issuer: IssuerId) -> Result<Amount, Error> {
        let acc = self
            .issuers
            .get(issuer as usize)
            .ok_or(Error::UnknownIssuer)?;
        if acc.owner != who {
            return Err(Error::NotAllowed);
        }
        if acc.retired {
            return Err(Error::Retired);
        }
        if self.height < acc.retire_at {
            return Err(Error::TooEarly);
        }
        let back = acc.esc.min(acc.locked);
        let unclaimed = acc.locked - back;
        self.transfer(POOL, who, back)?;
        self.transfer(POOL, TREASURY, unclaimed)?;

        let acc = &mut self.issuers[issuer as usize];
        acc.esc = 0;
        acc.locked = 0;
        acc.retired = true;
        Ok(back)
    }

    pub fn balance(&self, who: &str) -> Amount {
        self.balances.get(who).copied().unwrap_or(0)
    }

    /// Sum over the issuer's keys of `count` times the key's value.
    fn value_of(
        &self,
        issuer: IssuerId,
        count: impl Fn(&IssuerPerKeyTracking) -> Amount,
    ) -> Amount {
        self.issuers[issuer as usize]
            .keys
            .iter()
            .map(|&k| {
                let key = &self.keys[k as usize];
                count(key) * key.value
            })
            .sum()
    }

    fn transfer(&mut self, from: &str, to: &str, amount: Amount) -> Result<(), Error> {
        let bal = self.balances.entry(from.into()).or_default();
        *bal = bal.checked_sub(amount).ok_or(Error::InsufficientBalance)?;
        *self.balances.entry(to.into()).or_default() += amount;
        Ok(())
    }

    pub fn show(&self) {
        assert_eq!(
            self.balances.values().sum::<Amount>(),
            self.genesis,
            "supply doesn't add up"
        );
        let locked: Amount = self.issuers.iter().map(|i| i.locked).sum();
        assert_eq!(
            self.balance(POOL),
            self.held + locked,
            "pool doesn't add up"
        );

        println!(
            "\n  block {}   escrow_factor {}%   base_rate {}:{}   pool {} = held {} + locked {}   nullifiers {}",
            self.height,
            self.params.escrow_factor,
            self.params.base_rate.native,
            self.params.base_rate.bat,
            self.balance(POOL),
            self.held,
            locked,
            self.nullifiers.len()
        );
        let balances = self
            .balances
            .iter()
            .map(|(a, b)| format!("{a} {b}"))
            .collect::<Vec<_>>();
        println!("  balances: {}", balances.join(", "));
        println!(
            "  {:>2} {:<8} {:>5} {:>6} {:>4} {:>4} {:>9}",
            "id", "owner", "esc", "locked", "cap", "comm", "retire_at"
        );
        for (id, i) in self.issuers.iter().enumerate() {
            let retire = if i.retired {
                "retired".to_string()
            } else {
                i.retire_at.to_string()
            };
            println!(
                "  {:>2} {:<8} {:>5} {:>6} {:>4} {:>3}% {:>9}",
                id,
                i.owner,
                i.esc,
                i.locked,
                i.cap(self.params.escrow_factor),
                i.commission_percent,
                retire
            );
        }
        println!(
            "  {:>3} {:>6} {:>5} {:>5} {:>5} {:>6} {:>5} {:>4}",
            "key", "issuer", "denom", "value", "Niss", "Nspent", "Nref", "Δ"
        );
        for (id, k) in self.keys.iter().enumerate() {
            let delta = (k.n_spent + k.n_ref) as i64 - k.n_iss as i64;
            println!(
                "  {:>3} {:>6} {:>5} {:>5} {:>5} {:>6} {:>5} {:>4}",
                id, k.issuer, k.denom, k.value, k.n_iss, k.n_spent, k.n_ref, delta
            );
        }
        println!();
    }
}

fn distinct(nullifiers: &[BatNullifier]) -> bool {
    nullifiers.iter().collect::<BTreeSet<_>>().len() == nullifiers.len()
}

pub struct Issuer {
    pub owner: String,
    pub id: IssuerId,
    /// One per denomination, with the chain's id for it.
    keys: Vec<(KeyId, BatIssuerKeys)>,
    /// `k` per session, kept until the client's payment is final.
    sessions: BTreeMap<Sid, BatIssuerSession>,
}

impl Issuer {
    pub fn register<R: RngCore + CryptoRng>(
        rng: &mut R,
        chain: &mut Chain,
        owner: &str,
        esc: Amount,
        commission_percent: u32,
    ) -> Result<Self, Error> {
        let keys = chain
            .params
            .multipliers
            .iter()
            .map(|_| BatIssuerKeys::new(rng))
            .collect::<Vec<_>>();
        let pk_iss = keys
            .iter()
            .map(|k| k.public_key())
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| Error::BadKey)?;
        let id = chain.register_issuer(owner, &pk_iss, esc, commission_percent)?;
        let keys = chain.issuers[id as usize]
            .keys
            .iter()
            .copied()
            .zip(keys)
            .collect();
        Ok(Self {
            owner: owner.into(),
            id,
            keys,
            sessions: BTreeMap::new(),
        })
    }

    /// The chain's id of the key for the `denomination_index`th denomination.
    pub fn key(&self, denomination_index: usize) -> KeyId {
        self.keys[denomination_index].0
    }

    fn keypair(&self, key: KeyId) -> &BatIssuerKeys {
        &self
            .keys
            .iter()
            .find(|(id, _)| *id == key)
            .expect("not this issuer's key")
            .1
    }

    pub fn sign_blinded<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        key: KeyId,
        req: &BatIssueRequest,
    ) -> Result<BatIssueResponse, Error> {
        let (session, resp) = self
            .keypair(key)
            .sign(rng, key, req)
            .map_err(|_| Error::Malformed)?;
        self.sessions.insert(session.sid(), session);
        Ok(resp)
    }

    /// Refuses a request on chain that doesn't match what was signed, since `k` is public once
    /// posted even if the chain rejects it.
    pub fn reveal(&self, chain: &mut Chain, sid: Sid) -> Result<(), Error> {
        let s = chain.sessions.get(&sid).ok_or(Error::UnknownSession)?;
        let reveal = self.sessions[&sid]
            .clone()
            .reveal(&s.request)
            .map_err(|_| Error::SessionMismatch)?;
        chain.issue_for_issuer(&self.owner, &reveal)
    }

    /// Tokens the issuer signs for itself outside any session. The chain never counts them as
    /// issued.
    pub fn mint_off_books<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        denomination_index: usize,
        n: usize,
    ) -> Vec<BatPreToken> {
        let (key, keys) = &self.keys[denomination_index];
        let (session, req) = BatClientSession::new(rng, *key, n as u32).unwrap();
        let (issuer_session, resp) = keys.sign(rng, *key, &req).unwrap();
        let request = session.on_chain_issue_request(rng, &resp).unwrap();
        let reveal = issuer_session.reveal(&request).unwrap();
        session.unmask(&resp, &reveal).unwrap().0
    }
}

pub struct Client {
    pub account: String,
    pub sessions: BTreeMap<Sid, (BatClientSession, BatIssueResponse)>,
    pub refund_keys: BTreeMap<Sid, BatRefundKey>,
    pub tokens: Vec<BatPreToken>,
}

impl Client {
    pub fn new(account: &str) -> Self {
        Self {
            account: account.into(),
            sessions: BTreeMap::new(),
            refund_keys: BTreeMap::new(),
            tokens: Vec::new(),
        }
    }

    /// Blinds `l` fresh keys, has the issuer sign them under its `denomination_index`th key and
    /// pays. The tokens are usable once the issuer posts `k` and `unmask` is called.
    pub fn buy<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut Chain,
        issuer: &mut Issuer,
        denomination_index: usize,
        l: usize,
    ) -> Result<Sid, Error> {
        let key = issuer.key(denomination_index);
        let (session, req) =
            BatClientSession::new(rng, key, l as u32).map_err(|_| Error::Malformed)?;
        let resp = issuer.sign_blinded(rng, key, &req)?;
        let request = session
            .on_chain_issue_request(rng, &resp)
            .map_err(|_| Error::BadSignature)?;
        chain.issue_for_client(&self.account, &request)?;
        let sid = session.sid();
        self.sessions.insert(sid, (session, resp));
        Ok(sid)
    }

    pub fn unmask(&mut self, chain: &Chain, sid: Sid) {
        let SessionState::Issued { reveal, .. } = &chain.sessions[&sid].state else {
            panic!("k not on chain yet");
        };
        let (session, resp) = self.sessions.remove(&sid).unwrap();
        let (tokens, refund_key) = session.unmask(&resp, reveal).unwrap();
        self.refund_keys.insert(sid, refund_key);
        self.tokens.extend(tokens);
    }

    pub fn add_tokens(&mut self, tokens: Vec<BatPreToken>) {
        self.tokens.extend(tokens);
    }

    /// Total worth of the tokens in BAT.
    pub fn holdings(&self, chain: &Chain) -> Amount {
        self.tokens
            .iter()
            .map(|t| chain.keys[t.issuer as usize].denom)
            .sum()
    }

    /// Pays `amount` BAT using the largest denominations first, one batch signature for all tokens.
    pub fn pay<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut Chain,
        amount: Amount,
        ad: &[u8],
    ) -> Result<Payment, Error> {
        let denom = |t: &BatPreToken| chain.keys[t.issuer as usize].denom;
        let mut order = (0..self.tokens.len()).collect::<Vec<_>>();
        order.sort_by_key(|&i| std::cmp::Reverse(denom(&self.tokens[i])));
        let mut left = amount;
        let mut picked = Vec::new();
        for i in order {
            let d = denom(&self.tokens[i]);
            if d <= left {
                left -= d;
                picked.push(i);
            }
        }
        assert_eq!(
            left, 0,
            "{} can't make {amount} from its tokens",
            self.account
        );

        let tokens = picked
            .iter()
            .map(|&i| self.tokens[i].clone())
            .collect::<Vec<_>>();
        let payment = Payment {
            payment: BatFeePayment::<()>::new(rng, &tokens, ad).map_err(|_| Error::Malformed)?,
            ad: ad.to_vec(),
        };
        chain.spend(&payment)?;
        picked.sort_unstable_by(|a, b| b.cmp(a));
        for i in picked {
            self.tokens.remove(i);
        }
        Ok(payment)
    }

    /// Refund of `n` of the session's unspent tokens, signed with its refund key.
    pub fn refund_request<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        sid: Sid,
        n: usize,
    ) -> Result<BatRefundRequest, Error> {
        let unspent = self
            .tokens
            .iter()
            .filter(|t| t.sid == sid)
            .take(n)
            .cloned()
            .collect::<Vec<_>>();
        BatRefundRequest::<()>::new(rng, &self.refund_keys[&sid], &unspent)
            .map_err(|_| Error::Malformed)
    }

    /// Signs a refund for `tokens` with the session's refund key.
    pub fn refund_request_unchecked<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        sid: Sid,
        tokens: &[BatPreToken],
    ) -> BatRefundRequest {
        // Built by hand since `RefundRequest::new` refuses duplicate or no tokens.
        let refund_key = &self.refund_keys[&sid].0;
        let tokens = tokens.iter().map(|p| p.token.token()).collect::<Vec<_>>();
        let msg = RefundRequest::message(&sid, &tokens);
        let signature = BatchSig::new(
            rng,
            core::slice::from_ref(&refund_key.keypair),
            &msg,
            &bat_signature_base(),
        )
        .unwrap();
        BatRefundRequest::<()>::try_from(&RefundRequest {
            sid,
            tokens,
            signature,
        })
        .unwrap()
    }

    /// Submits `req` and drops the tokens it refunds.
    pub fn submit_refund(
        &mut self,
        chain: &mut Chain,
        req: &BatRefundRequest,
    ) -> Result<Amount, Error> {
        let value = chain.refund(req)?;
        let refunded = req.tokens.iter().map(|t| t.pk_e).collect::<BTreeSet<_>>();
        self.tokens
            .retain(|t| !t.nullifier().is_ok_and(|n| refunded.contains(&n)));
        Ok(value)
    }

    pub fn refund<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut Chain,
        sid: Sid,
    ) -> Result<Amount, Error> {
        self.refund_some(rng, chain, sid, usize::MAX)
    }

    /// Refunds `n` of the session's unspent tokens. The rest can still be spent but not refunded.
    pub fn refund_some<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut Chain,
        sid: Sid,
        n: usize,
    ) -> Result<Amount, Error> {
        let req = self.refund_request(rng, sid, n)?;
        self.submit_refund(chain, &req)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    BadKey,
    BadRate,
    UnknownIssuer,
    NotAllowed,
    InsufficientBalance,
    SessionExists,
    UnknownSession,
    NotAwaitingIssuer,
    SessionMismatch,
    WrongK,
    OverCapacity,
    IssuanceFrozen,
    Retired,
    TooEarly,
    Malformed,
    DuplicateToken,
    AlreadySpent,
    BadSignature,
    NotIssued,
    AlreadyRefunded,
    Insolvent,
}

#[derive(Clone, Copy, Debug, clap::ValueEnum)]
pub enum Scenario {
    /// Buy 10, spend 3, refund 7, retire
    Happy,
    /// Spend part, refund the rest, and a partial refund that gives up the remainder
    Refund,
    /// Issuer never posts k, client takes back its payment and the commission
    Reclaim,
    /// Refund 10 copies of one token
    RefundDuplicates,
    /// Refund self-signed tokens through another issuer's session
    SessionIssuerSwap,
    /// Tokens signed under the 100 key, request on chain names the 1 key
    DenominationSwap,
    /// Issuer spends its own free tokens up to the cap and locks clients out
    Capacity,
    /// Buy the whole cap and refund it at once, losing only the commission
    CapacityGrief,
    /// One issuer's free tokens are paid out of its own share of the pool only
    PoolIsolation,
    /// Retirement notice, issuance freeze and reclaim
    Retirement,
    /// Tokens nobody spent or refunded go to the treasury at retirement
    Breakage,
    /// One payment across three denomination keys
    Denominations,
    /// Denominations scaled from 1 native for 2 BAT, then a rate change
    Rate,
    /// Issuer locks more escrow to issue past its cap
    TopUp,
}

pub fn run(which: Option<Scenario>) {
    use clap::ValueEnum;
    let scenarios = match which {
        Some(s) => vec![s],
        None => Scenario::value_variants().to_vec(),
    };
    for s in scenarios {
        match s {
            Scenario::Happy => happy(),
            Scenario::Refund => refund(),
            Scenario::Reclaim => reclaim(),
            Scenario::RefundDuplicates => refund_duplicates(),
            Scenario::SessionIssuerSwap => session_issuer_swap(),
            Scenario::DenominationSwap => denomination_swap(),
            Scenario::Capacity => capacity(),
            Scenario::CapacityGrief => capacity_grief(),
            Scenario::PoolIsolation => pool_isolation(),
            Scenario::Retirement => retirement(),
            Scenario::Breakage => breakage(),
            Scenario::Denominations => denominations(),
            Scenario::Rate => rate(),
            Scenario::TopUp => top_up(),
        }
    }
}

fn setup() -> (ChaCha20Rng, Chain) {
    setup_with(SystemParams::default())
}

fn setup_with(params: SystemParams) -> (ChaCha20Rng, Chain) {
    let chain = Chain::new(
        params,
        &[
            ("acme", 10_000),
            ("issuer", 10_000),
            ("alice", 1_000),
            ("bob", 1_000),
            ("mallory", 1_000),
        ],
    );
    (ChaCha20Rng::seed_from_u64(0), chain)
}

fn ok<T>(what: &str, r: Result<T, Error>) -> T {
    match r {
        Ok(v) => {
            println!("  {what:<70} ok");
            v
        }
        Err(e) => panic!("{what}: unexpected {e:?}"),
    }
}

fn rejected<T>(what: &str, r: Result<T, Error>, want: Error) {
    match r {
        Err(e) if e == want => println!("  {what:<70} rejected, {e:?}"),
        Err(e) => panic!("{what}: rejected with {e:?}, expected {want:?}"),
        Ok(_) => panic!("{what}: accepted, expected {want:?}"),
    }
}

fn happy() {
    println!("\n== Buy 10, spend 3, refund 7 ==\n");
    let (mut rng, mut chain) = setup();
    let mut acme = ok(
        "acme registers a key for denomination 1 with escrow 20",
        Issuer::register(&mut rng, &mut chain, "acme", 20, 0),
    );
    let mut alice = Client::new("alice");
    let sid = ok(
        "alice pays for 10 tokens",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    chain.show();

    ok("acme posts k", acme.reveal(&mut chain, sid));
    alice.unmask(&chain, sid);
    chain.show();

    let p = ok(
        "alice pays a fee of 3",
        alice.pay(&mut rng, &mut chain, 3, b"tx 1"),
    );
    rejected(
        "someone replays that payment",
        chain.spend(&p),
        Error::AlreadySpent,
    );
    let req = alice.refund_request(&mut rng, sid, usize::MAX).unwrap();
    ok(
        "alice refunds the other 7",
        alice.submit_refund(&mut chain, &req),
    );
    rejected(
        "someone replays that refund",
        chain.refund(&req),
        Error::AlreadyRefunded,
    );
    chain.show();

    chain.advance_to(100);
    let back = ok("block 100, acme retires", chain.retire("acme", acme.id));
    assert_eq!(back, 20);
    chain.show();
}

fn refund() {
    println!("\n== Refunds and commission ==\n");
    let (mut rng, mut chain) = setup();
    let mut acme = ok(
        "acme registers a key with escrow 40 and commission 10%",
        Issuer::register(&mut rng, &mut chain, "acme", 40, 10),
    );
    let mut alice = Client::new("alice");
    let sid = ok(
        "alice pays 10 for 10 tokens and 1 commission",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    ok(
        "acme posts k and gets the commission",
        acme.reveal(&mut chain, sid),
    );
    alice.unmask(&chain, sid);
    ok(
        "alice pays a fee of 4",
        alice.pay(&mut rng, &mut chain, 4, b"tx 1"),
    );
    let req = alice.refund_request(&mut rng, sid, usize::MAX).unwrap();
    let back = ok(
        "alice refunds the other 6, the commission stays with acme",
        alice.submit_refund(&mut chain, &req),
    );
    assert_eq!(back, 6);
    rejected(
        "someone replays that refund",
        chain.refund(&req),
        Error::AlreadyRefunded,
    );
    chain.show();

    let mut bob = Client::new("bob");
    let sid = ok(
        "bob pays 10 for 10 tokens and 1 commission",
        bob.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    ok("acme posts k", acme.reveal(&mut chain, sid));
    bob.unmask(&chain, sid);
    ok(
        "bob pays a fee of 2",
        bob.pay(&mut rng, &mut chain, 2, b"tx 2"),
    );
    ok(
        "bob refunds 3 of his 8",
        bob.refund_some(&mut rng, &mut chain, sid, 3),
    );
    ok(
        "bob pays a fee of 2 with tokens he kept",
        bob.pay(&mut rng, &mut chain, 2, b"tx 3"),
    );
    rejected(
        "bob refunds his last 3",
        bob.refund(&mut rng, &mut chain, sid),
        Error::AlreadyRefunded,
    );
    chain.show();

    chain.advance_to(100);
    let back = ok(
        "block 100, acme retires, bob's last 3 go to the treasury",
        chain.retire("acme", acme.id),
    );
    assert_eq!(back, 40);
    // 8 in fees and bob's last 3.
    assert_eq!(chain.balance(TREASURY), 11);
    assert_eq!(chain.balance("acme"), 10_002);
    assert_eq!(chain.balance("alice"), 995);
    chain.show();
}

fn reclaim() {
    println!("\n== Issuer never posts k ==\n");
    let (mut rng, mut chain) = setup();
    let mut acme = ok(
        "acme registers a key with escrow 20 and commission 10%",
        Issuer::register(&mut rng, &mut chain, "acme", 20, 10),
    );
    let mut alice = Client::new("alice");
    let sid = ok(
        "alice pays 10 for 10 tokens and 1 commission",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    rejected(
        "alice asks for her payment back",
        chain.reclaim("alice", sid),
        Error::TooEarly,
    );
    chain.show();

    chain.advance_to(5);
    ok(
        "block 5, acme still hasn't posted k, alice asks again",
        chain.reclaim("alice", sid),
    );
    assert_eq!(chain.balance("alice"), 1_000);
    rejected(
        "acme posts k late",
        acme.reveal(&mut chain, sid),
        Error::NotAwaitingIssuer,
    );
    rejected(
        "alice asks once more",
        chain.reclaim("alice", sid),
        Error::NotAwaitingIssuer,
    );
    chain.show();
}

fn refund_duplicates() {
    println!("\n== Refund 10 copies of one token ==\n");
    let (mut rng, mut chain) = setup();
    let mut acme = ok(
        "acme registers a key with escrow 20",
        Issuer::register(&mut rng, &mut chain, "acme", 20, 0),
    );
    let mut alice = Client::new("alice");
    let sid = ok(
        "alice pays for 10 tokens",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    ok("acme posts k", acme.reveal(&mut chain, sid));
    alice.unmask(&chain, sid);
    ok(
        "alice pays a fee of 9",
        alice.pay(&mut rng, &mut chain, 9, b"tx 1"),
    );

    let last = alice.tokens[0].clone();
    let req = alice.refund_request_unchecked(&mut rng, sid, &vec![last; 10]);
    rejected(
        "alice refunds 10 copies of her last token",
        chain.refund(&req),
        Error::DuplicateToken,
    );
    ok(
        "alice refunds just the one",
        alice.refund(&mut rng, &mut chain, sid),
    );

    chain.advance_to(100);
    let back = ok("block 100, acme retires", chain.retire("acme", acme.id));
    assert_eq!(back, 20);
    chain.show();
}

fn session_issuer_swap() {
    println!("\n== Refund through another issuer's session ==\n");
    let (mut rng, mut chain) = setup();
    let mut acme = ok(
        "acme registers a key with escrow 20",
        Issuer::register(&mut rng, &mut chain, "acme", 20, 0),
    );
    let shady = ok(
        "mallory registers her own key with no escrow",
        Issuer::register(&mut rng, &mut chain, "mallory", 0, 0),
    );
    let mut mallory = Client::new("mallory");
    let sid = ok(
        "mallory pays acme for 10 tokens",
        mallory.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    ok("acme posts k", acme.reveal(&mut chain, sid));
    mallory.unmask(&chain, sid);

    let free = shady.mint_off_books(&mut rng, 0, 10);
    let req = mallory.refund_request_unchecked(&mut rng, sid, &free);
    // Refund checks tokens against the session's key, acme's, so hers don't verify.
    rejected(
        "mallory refunds 10 self-signed tokens through acme's session",
        chain.refund(&req),
        Error::BadSignature,
    );
    ok(
        "mallory spends acme's 10 tokens",
        mallory.pay(&mut rng, &mut chain, 10, b"tx 1"),
    );

    chain.advance_to(100);
    let back = ok("block 100, acme retires", chain.retire("acme", acme.id));
    assert_eq!(back, 20);
    ok("mallory retires her key", chain.retire("mallory", shady.id));
    chain.show();
}

fn denomination_swap() {
    println!("\n== Signed under one denomination, paid for another ==\n");
    let params = SystemParams {
        multipliers: vec![1, 100],
        ..Default::default()
    };
    let (mut rng, mut chain) = setup_with(params);
    let mut acme = ok(
        "acme registers keys for denominations 1 and 100 with escrow 1000",
        Issuer::register(&mut rng, &mut chain, "acme", 1000, 0),
    );
    let (large, small) = (acme.key(1), acme.key(0));
    let (session, req) = BatClientSession::new(&mut rng, large, 5).unwrap();
    let resp = ok(
        "mallory has acme sign 5 tokens under the 100 key",
        acme.sign_blinded(&mut rng, large, &req),
    );
    let mut request = session.on_chain_issue_request(&mut rng, &resp).unwrap();
    request.issuer = small;
    ok(
        "mallory posts a request naming the 1 key and pays 5",
        chain.issue_for_client("mallory", &request),
    );
    rejected(
        "acme posts k",
        acme.reveal(&mut chain, request.sid),
        Error::SessionMismatch,
    );
    println!("  had acme posted k, the chain would reject it as WrongK with k already public,");
    println!("  and mallory would unmask 5 tokens of 100 and reclaim her 5");

    chain.advance_to(5);
    ok(
        "block 5, mallory takes her payment back",
        chain.reclaim("mallory", request.sid),
    );
    assert_eq!(chain.balance("mallory"), 1_000);
    chain.show();
}

fn capacity() {
    println!("\n== Issuer uses up the cap with its own tokens ==\n");
    let (mut rng, mut chain) = setup();
    let mut acme = ok(
        "acme registers a key with escrow 20, so cap 10",
        Issuer::register(&mut rng, &mut chain, "acme", 20, 0),
    );
    let mut alice = Client::new("alice");
    let sid = ok(
        "alice pays for 10 tokens",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    ok("acme posts k", acme.reveal(&mut chain, sid));
    alice.unmask(&chain, sid);

    let mut acme_client = Client::new("acme");
    acme_client.add_tokens(acme.mint_off_books(&mut rng, 0, 10));
    ok(
        "acme spends 10 tokens it signed for itself",
        acme_client.pay(&mut rng, &mut chain, 10, b"acme tx"),
    );
    rejected(
        "alice pays a fee of 1",
        alice.pay(&mut rng, &mut chain, 1, b"tx 1"),
        Error::OverCapacity,
    );
    ok(
        "alice refunds all 10 instead",
        alice.refund(&mut rng, &mut chain, sid),
    );
    chain.show();

    chain.advance_to(100);
    let back = ok("block 100, acme retires", chain.retire("acme", acme.id));
    // acme's free fees come out of its own escrow, alice is whole.
    assert_eq!(back, 10);
    assert_eq!(chain.balances["alice"], 1_000);
    chain.show();
}

fn capacity_grief() {
    println!("\n== Buy the whole cap and refund it at once ==\n");
    let (mut rng, mut chain) = setup();
    let mut acme = ok(
        "acme registers a key with escrow 20, so cap 10, and commission 10%",
        Issuer::register(&mut rng, &mut chain, "acme", 20, 10),
    );
    let mut mallory = Client::new("mallory");
    let sid = ok(
        "mallory pays 10 for 10 tokens and 1 commission",
        mallory.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    ok("acme posts k", acme.reveal(&mut chain, sid));
    mallory.unmask(&chain, sid);
    ok(
        "mallory refunds all 10 straight away",
        mallory.refund(&mut rng, &mut chain, sid),
    );
    assert_eq!(chain.balance("mallory"), 999);

    let mut alice = Client::new("alice");
    let late = ok(
        "alice pays 1 for 1 token and 1 commission, rounded up",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 1),
    );
    rejected(
        "acme posts k, but Niss never goes down",
        acme.reveal(&mut chain, late),
        Error::OverCapacity,
    );
    chain.show();

    chain.advance_to(100);
    ok(
        "block 100, alice takes her payment back",
        chain.reclaim("alice", late),
    );
    let back = ok("acme retires", chain.retire("acme", acme.id));
    assert_eq!(back, 20);
    assert_eq!(chain.balance("acme"), 10_001);
    chain.show();
}

fn pool_isolation() {
    println!("\n== Free tokens are paid out of their issuer's share of the pool ==\n");
    let (mut rng, mut chain) = setup();
    let mut acme = ok(
        "acme registers a key with escrow 20, so cap 10",
        Issuer::register(&mut rng, &mut chain, "acme", 20, 0),
    );
    let mut issuer = ok(
        "issuer registers a key with escrow 20, so cap 10",
        Issuer::register(&mut rng, &mut chain, "issuer", 20, 0),
    );
    let mut alice = Client::new("alice");
    let mut bob = Client::new("bob");
    let a = ok(
        "alice pays acme for 10 tokens",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    let b = ok(
        "bob pays issuer for 10 tokens",
        bob.buy(&mut rng, &mut chain, &mut issuer, 0, 10),
    );
    ok("acme posts k", acme.reveal(&mut chain, a));
    alice.unmask(&chain, a);
    ok("issuer posts k", issuer.reveal(&mut chain, b));
    bob.unmask(&chain, b);

    let mut acme_client = Client::new("acme");
    acme_client.add_tokens(acme.mint_off_books(&mut rng, 0, 10));
    ok(
        "acme spends 10 tokens it signed for itself",
        acme_client.pay(&mut rng, &mut chain, 10, b"acme tx"),
    );
    rejected(
        "alice pays a fee of 1",
        alice.pay(&mut rng, &mut chain, 1, b"tx 1"),
        Error::OverCapacity,
    );
    ok(
        "bob pays a fee of 4",
        bob.pay(&mut rng, &mut chain, 4, b"tx 2"),
    );
    ok(
        "alice refunds all 10 out of acme's share",
        alice.refund(&mut rng, &mut chain, a),
    );
    ok(
        "bob refunds the other 6",
        bob.refund(&mut rng, &mut chain, b),
    );
    chain.show();

    chain.advance_to(100);
    let back = ok("block 100, acme retires", chain.retire("acme", acme.id));
    assert_eq!(back, 10);
    let back = ok("issuer retires", chain.retire("issuer", issuer.id));
    assert_eq!(back, 20);
    assert_eq!(chain.balance(POOL), 0);
    chain.show();
}

fn retirement() {
    println!("\n== Retirement, issuance freeze and reclaim ==\n");
    let (mut rng, mut chain) = setup();
    let mut acme = ok(
        "acme registers at block 0, can retire from block 100",
        Issuer::register(&mut rng, &mut chain, "acme", 40, 0),
    );
    rejected(
        "acme retires straight away",
        chain.retire("acme", acme.id),
        Error::TooEarly,
    );
    let mut alice = Client::new("alice");
    let sid = ok(
        "alice pays for 10 tokens",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    ok("acme posts k", acme.reveal(&mut chain, sid));
    alice.unmask(&chain, sid);

    chain.advance_to(91);
    let late = ok(
        "block 91, alice pays for 5 more",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 5),
    );
    rejected(
        "acme posts k, but issuance is frozen 10 blocks before retirement",
        acme.reveal(&mut chain, late),
        Error::IssuanceFrozen,
    );
    rejected(
        "alice asks for her payment back",
        chain.reclaim("alice", late),
        Error::TooEarly,
    );
    chain.show();

    chain.advance_to(96);
    ok("block 96, alice asks again", chain.reclaim("alice", late));
    ok(
        "alice pays a fee of 4",
        alice.pay(&mut rng, &mut chain, 4, b"tx 1"),
    );
    ok(
        "alice refunds the other 6",
        alice.refund(&mut rng, &mut chain, sid),
    );

    chain.advance_to(100);
    ok("block 100, acme retires", chain.retire("acme", acme.id));
    rejected(
        "alice pays for more tokens",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 1),
        Error::Retired,
    );
    chain.show();
}

fn breakage() {
    println!("\n== Unclaimed tokens go to the treasury at retirement ==\n");
    let (mut rng, mut chain) = setup();
    let mut acme = ok(
        "acme registers a key with escrow 20",
        Issuer::register(&mut rng, &mut chain, "acme", 20, 0),
    );
    let mut alice = Client::new("alice");
    let sid = ok(
        "alice pays for 10 tokens",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    ok("acme posts k", acme.reveal(&mut chain, sid));
    alice.unmask(&chain, sid);
    ok(
        "alice pays a fee of 2 and goes offline",
        alice.pay(&mut rng, &mut chain, 2, b"tx 1"),
    );
    chain.show();

    chain.advance_to(100);
    let back = ok("block 100, acme retires", chain.retire("acme", acme.id));
    assert_eq!(back, 20);
    // 2 in fees and alice's other 8.
    assert_eq!(chain.balance(TREASURY), 10);
    rejected(
        "alice comes back and refunds",
        alice.refund(&mut rng, &mut chain, sid),
        Error::Retired,
    );
    rejected(
        "alice pays a fee of 1",
        alice.pay(&mut rng, &mut chain, 1, b"tx 2"),
        Error::Retired,
    );
    chain.show();
}

fn denominations() {
    println!("\n== Denominations 1, 10 and 100 under one escrow ==\n");
    let params = SystemParams {
        multipliers: vec![1, 10, 100],
        ..Default::default()
    };
    let (mut rng, mut chain) = setup_with(params);
    let mut acme = ok(
        "acme registers keys for denominations 1, 10 and 100 with escrow 600",
        Issuer::register(&mut rng, &mut chain, "acme", 600, 0),
    );
    let mut alice = Client::new("alice");
    for (i, l) in [9, 9, 2].into_iter().enumerate() {
        let sid = ok(
            &format!(
                "alice pays for {l} tokens of {}",
                chain.keys[acme.key(i) as usize].denom
            ),
            alice.buy(&mut rng, &mut chain, &mut acme, i, l),
        );
        ok("acme posts k", acme.reveal(&mut chain, sid));
        alice.unmask(&chain, sid);
    }
    chain.show();

    let p = ok(
        "alice pays a fee of 123",
        alice.pay(&mut rng, &mut chain, 123, b"tx 1"),
    );
    let used = p.payment.issuers();
    println!(
        "  that was {} tokens under {} keys, so a {}-pair pairing check",
        p.payment.tokens.len(),
        used.len(),
        used.len() + 1
    );
    chain.show();
}

fn rate() {
    println!("\n== Denominations scaled from 1 native for 2 BAT ==\n");
    let params = SystemParams {
        base_rate: Rate { native: 1, bat: 2 },
        multipliers: vec![1, 10],
        ..Default::default()
    };
    let (mut rng, mut chain) = setup_with(params);
    let mut acme = ok(
        "acme registers 2 and 20 BAT keys, worth 1 and 10 native, escrow 100",
        Issuer::register(&mut rng, &mut chain, "acme", 100, 0),
    );
    let mut alice = Client::new("alice");
    let small = ok(
        "alice locks 10 native for 10 tokens of 2 BAT",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    let large = ok(
        "alice locks 10 native for 1 token of 20 BAT",
        alice.buy(&mut rng, &mut chain, &mut acme, 1, 1),
    );
    for sid in [small, large] {
        ok("acme posts k", acme.reveal(&mut chain, sid));
        alice.unmask(&chain, sid);
    }
    println!("  alice holds {} BAT", alice.holdings(&chain));
    let before = chain.balance(TREASURY);
    ok(
        "alice pays a fee of 24 BAT",
        alice.pay(&mut rng, &mut chain, 24, b"tx 1"),
    );
    println!("  that unlocked {} native", chain.balance(TREASURY) - before);
    chain.show();

    ok(
        "governance sets the base rate to 1 native for 4 BAT",
        chain.set_base_rate(Rate { native: 1, bat: 4 }),
    );
    let mut issuer = ok(
        "issuer registers 4 and 40 BAT keys, worth 1 and 10 native, escrow 100",
        Issuer::register(&mut rng, &mut chain, "issuer", 100, 0),
    );
    let sid = ok(
        "alice locks 5 native for 5 tokens of 4 BAT",
        alice.buy(&mut rng, &mut chain, &mut issuer, 0, 5),
    );
    ok("issuer posts k", issuer.reveal(&mut chain, sid));
    alice.unmask(&chain, sid);
    println!("  alice holds {} BAT", alice.holdings(&chain));
    let before = chain.balance(TREASURY);
    ok(
        "alice pays a fee of 28 BAT with tokens from both",
        alice.pay(&mut rng, &mut chain, 28, b"tx 2"),
    );
    let unlocked = chain.balance(TREASURY) - before;
    println!(
        "  that unlocked {unlocked} native, 1 per 4 BAT from issuer and 1 per 2 BAT from acme"
    );
    assert_eq!(unlocked, 9);
    let back = ok(
        "alice refunds her last 4 tokens of 2 BAT",
        alice.refund(&mut rng, &mut chain, small),
    );
    assert_eq!(back, 4);
    chain.show();

    chain.advance_to(100);
    let back = ok("block 100, acme retires", chain.retire("acme", acme.id));
    assert_eq!(back, 100);
    let back = ok("issuer retires", chain.retire("issuer", issuer.id));
    assert_eq!(back, 100);
    assert_eq!(chain.balance(TREASURY), 21);
    assert_eq!(chain.balance(POOL), 0);
    chain.show();
}

fn top_up() {
    println!("\n== Issuer tops up escrow to issue more ==\n");
    let (mut rng, mut chain) = setup();
    let mut acme = ok(
        "acme registers a key with escrow 20, so cap 10",
        Issuer::register(&mut rng, &mut chain, "acme", 20, 0),
    );
    let mut alice = Client::new("alice");
    let first = ok(
        "alice pays for 10 tokens",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 10),
    );
    ok("acme posts k", acme.reveal(&mut chain, first));
    let second = ok(
        "alice pays for 5 more",
        alice.buy(&mut rng, &mut chain, &mut acme, 0, 5),
    );
    rejected(
        "acme posts k",
        acme.reveal(&mut chain, second),
        Error::OverCapacity,
    );
    rejected(
        "mallory tops up acme's escrow",
        chain.top_up_escrow("mallory", acme.id, 10),
        Error::NotAllowed,
    );
    ok(
        "acme locks 10 more, so cap 15",
        chain.top_up_escrow("acme", acme.id, 10),
    );
    ok("acme posts k again", acme.reveal(&mut chain, second));
    alice.unmask(&chain, first);
    alice.unmask(&chain, second);
    chain.show();

    ok(
        "alice pays a fee of 15",
        alice.pay(&mut rng, &mut chain, 15, b"tx 1"),
    );
    chain.advance_to(100);
    let back = ok("block 100, acme retires", chain.retire("acme", acme.id));
    assert_eq!(back, 30);
    rejected(
        "acme tops up the retired key",
        chain.top_up_escrow("acme", acme.id, 10),
        Error::Retired,
    );
    chain.show();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn happy_path() {
        happy();
    }

    #[test]
    fn refund_keeps_commission_and_gives_up_the_rest() {
        refund();
    }

    #[test]
    fn reclaim_returns_payment_and_commission() {
        reclaim();
    }

    #[test]
    fn refund_rejects_duplicates() {
        refund_duplicates();
    }

    #[test]
    fn refund_bound_to_session_issuer() {
        session_issuer_swap();
    }

    #[test]
    fn reveal_bound_to_requested_key() {
        denomination_swap();
    }

    #[test]
    fn issuer_uses_up_capacity() {
        capacity();
    }

    #[test]
    fn grief_costs_the_commission() {
        capacity_grief();
    }

    #[test]
    fn issuers_isolated_in_pool() {
        pool_isolation();
    }

    #[test]
    fn retirement_and_reclaim() {
        retirement();
    }

    #[test]
    fn unclaimed_to_treasury() {
        breakage();
    }

    #[test]
    fn denomination_pools() {
        denominations();
    }

    #[test]
    fn rate_scales_denominations() {
        rate();
    }

    #[test]
    fn top_up_raises_cap() {
        top_up();
    }
}
