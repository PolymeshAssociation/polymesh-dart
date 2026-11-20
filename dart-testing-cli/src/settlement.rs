//! The settlement state machine, mirroring
//! `Polymesh/pallets/confidential-assets/src/settlement.rs`.
//!
//! The CLI previously tracked a single status per party and merged it into the settlement status;
//! that is not how the pallet works. The pallet keeps per-party `LegAffirmationStatus` entries plus
//! two settlement counters (`SettlementPendingAffirmations`, `SettlementPendingFinalizations`), and
//! executes/finalizes when those counters reach zero. This module reproduces that, including the
//! exact error for each transition.

use rusqlite::params;

use polymesh_dart::{LegEncrypted, LegId, LegRef, MediatorId, SettlementRef};

use crate::errors::{ChainError, ChainFailure, ChainResult};
use crate::storage::Store;

/// The affirmation status for each party in a settlement leg (`pallet::AffirmationStatus`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AffirmationStatus {
    Pending,
    Affirmed,
    Rejected,
    Finalized,
}

impl AffirmationStatus {
    fn name(&self) -> &'static str {
        match self {
            AffirmationStatus::Pending => "Pending",
            AffirmationStatus::Affirmed => "Affirmed",
            AffirmationStatus::Rejected => "Rejected",
            AffirmationStatus::Finalized => "Finalized",
        }
    }

    fn from_name(s: &str) -> ChainResult<Self> {
        match s {
            "Pending" => Ok(AffirmationStatus::Pending),
            "Affirmed" => Ok(AffirmationStatus::Affirmed),
            "Rejected" => Ok(AffirmationStatus::Rejected),
            "Finalized" => Ok(AffirmationStatus::Finalized),
            _ => Err(ChainFailure::Internal(format!(
                "bad affirmation status: {s}"
            ))),
        }
    }
}

/// Settlement status (`pallet::SettlementStatus`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SettlementStatus {
    Pending,
    Executed,
    Rejected,
    Finalized,
}

impl SettlementStatus {
    fn name(&self) -> &'static str {
        match self {
            SettlementStatus::Pending => "Pending",
            SettlementStatus::Executed => "Executed",
            SettlementStatus::Rejected => "Rejected",
            SettlementStatus::Finalized => "Finalized",
        }
    }

    fn from_name(s: &str) -> ChainResult<Self> {
        match s {
            "Pending" => Ok(SettlementStatus::Pending),
            "Executed" => Ok(SettlementStatus::Executed),
            "Rejected" => Ok(SettlementStatus::Rejected),
            "Finalized" => Ok(SettlementStatus::Finalized),
            _ => Err(ChainFailure::Internal(format!(
                "bad settlement status: {s}"
            ))),
        }
    }
}

/// Leg affirmation party (`pallet::LegAffirmParty`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LegAffirmParty {
    Sender,
    Receiver,
    Mediator(MediatorId),
}

impl LegAffirmParty {
    fn is_mediator(&self) -> bool {
        matches!(self, LegAffirmParty::Mediator(_))
    }

    fn name(&self) -> String {
        match self {
            LegAffirmParty::Sender => "Sender".to_string(),
            LegAffirmParty::Receiver => "Receiver".to_string(),
            LegAffirmParty::Mediator(id) => format!("Mediator({id})"),
        }
    }
}

/// Pending counts (`pallet::PendingCounts`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PendingCounts {
    pub affirms: u32,
    pub finals: u32,
}

/// The settlement status snapshot for one dispatch, mirroring `UpdateSettlementStatus<T>`.
pub struct Settlement<'a> {
    store: &'a Store,
    pub settlement_ref: SettlementRef,
    pub leg_id: LegId,
    pub status: SettlementStatus,
}

impl<'a> Settlement<'a> {
    /// `UpdateSettlementStatus::new(leg_ref)`: reads the settlement status, erroring with
    /// `SettlementNotFound`.
    pub fn new(store: &'a Store, leg_ref: &LegRef) -> ChainResult<Self> {
        let status = store
            .row_text(
                "SELECT status FROM settlement_state WHERE settlement_ref = ?1",
                params![leg_ref.settlement.0.to_vec()],
            )?
            .map(|s| SettlementStatus::from_name(&s))
            .transpose()?
            .ok_or(ChainFailure::Error(ChainError::SettlementNotFound))?;

        Ok(Self {
            store,
            settlement_ref: leg_ref.settlement,
            leg_id: leg_ref.leg_id,
            status,
        })
    }

    pub fn ensure_pending(&self) -> ChainResult<()> {
        if self.status != SettlementStatus::Pending {
            return Err(ChainFailure::Error(ChainError::SettlementNotPending));
        }
        Ok(())
    }

    /// The settlement status snapshot taken when this instance was created
    /// (`UpdateSettlementStatus::new`).
    pub fn status(&self) -> SettlementStatus {
        self.status
    }

    /// `ensure_settlement_executed`: sender/counter and claim paths require `Executed`.
    pub fn ensure_executed(&self) -> ChainResult<()> {
        if self.status != SettlementStatus::Executed {
            return Err(ChainFailure::Error(ChainError::SettlementNotExecuted));
        }
        Ok(())
    }

    /// The revert-affirmation guard (`settlement.rs:441-446`): a revert is accepted while the
    /// settlement is `Pending` (the revert then rejects it) or `Rejected`; any other status is
    /// `SettlementAlreadyExecuted`.
    pub fn ensure_revertable(&self) -> ChainResult<()> {
        if !matches!(
            self.status,
            SettlementStatus::Pending | SettlementStatus::Rejected
        ) {
            return Err(ChainFailure::Error(ChainError::SettlementAlreadyExecuted));
        }
        Ok(())
    }

    /// `SettlementLegs::get((settlement_ref, leg_id))` — `LegNotFound` when the leg is absent
    /// (including after finalization pruning).
    pub fn encrypted_leg(&self) -> ChainResult<LegEncrypted> {
        self.store
            .settlement_leg(&self.settlement_ref, self.leg_id)?
            .ok_or(ChainFailure::Error(ChainError::LegNotFound))
    }

    /// `SettlementLegs::get((settlement_ref, leg_id))`.
    pub fn leg_count(&self) -> ChainResult<u32> {
        u32::try_from(self.store.row_i64(
            "SELECT leg_count FROM settlement_leg_count WHERE settlement_ref = ?1",
            params![self.settlement_ref.0.to_vec()],
        )?)
        .map_err(|_| ChainFailure::Error(ChainError::LegNotFound))
    }

    // -------------------------------------------------- party statuses

    pub fn party_status(&self, party: LegAffirmParty) -> ChainResult<Option<AffirmationStatus>> {
        self.store
            .row_text(
                "SELECT status FROM leg_affirmation_status
                 WHERE settlement_ref = ?1 AND leg_id = ?2 AND party = ?3",
                params![
                    self.settlement_ref.0.to_vec(),
                    self.leg_id as i64,
                    party.name()
                ],
            )?
            .map(|s| AffirmationStatus::from_name(&s))
            .transpose()
    }

    /// `set_party_status`: the expected-old-status check plus the pending-finalizations counter, with
    /// the pallet's exact error for each mismatch.
    pub fn set_party_status(
        &self,
        party: LegAffirmParty,
        expected_old: AffirmationStatus,
        new: AffirmationStatus,
    ) -> ChainResult<u32> {
        let current = self.party_status(party)?;

        if current == Some(expected_old) {
            self.store.conn.execute(
                "UPDATE leg_affirmation_status SET status = ?4
                 WHERE settlement_ref = ?1 AND leg_id = ?2 AND party = ?3",
                params![
                    self.settlement_ref.0.to_vec(),
                    self.leg_id as i64,
                    party.name(),
                    new.name()
                ],
            )?;
        } else if let Some(current) = current {
            return Err(ChainFailure::Error(match (current, party) {
                (AffirmationStatus::Rejected, _) => ChainError::AlreadyRejected,
                (AffirmationStatus::Finalized, _) => ChainError::AlreadyFinalized,
                (AffirmationStatus::Affirmed, p) if p.is_mediator() => ChainError::AlreadyAffirmed,
                _ => ChainError::InvalidAffirmationStatusTransition,
            }));
        } else if party.is_mediator() {
            return Err(ChainFailure::Error(ChainError::WrongMediatorId));
        } else {
            return Err(ChainFailure::Error(ChainError::LegNotFound));
        }

        // `SettlementPendingFinalizations` only moves for sender/receiver transitions.
        let pending_final = match (party, expected_old, new) {
            (
                LegAffirmParty::Sender | LegAffirmParty::Receiver,
                AffirmationStatus::Pending,
                AffirmationStatus::Affirmed,
            ) => self.add_pending_finalizations(1)?,
            (
                LegAffirmParty::Sender | LegAffirmParty::Receiver,
                AffirmationStatus::Affirmed,
                AffirmationStatus::Finalized,
            ) => self.sub_pending_finalizations(1)?,
            _ => self.pending_finalizations()?,
        };
        Ok(pending_final)
    }

    /// `party_affirms`: transition plus the pending-affirmations counter.
    pub fn party_affirms(
        &self,
        party: LegAffirmParty,
        accept: bool,
        is_instant: bool,
    ) -> ChainResult<PendingCounts> {
        let new = match (accept, is_instant) {
            (true, true) => AffirmationStatus::Finalized,
            (true, false) => AffirmationStatus::Affirmed,
            (false, _) => AffirmationStatus::Rejected,
        };
        let pending_final = self.set_party_status(party, AffirmationStatus::Pending, new)?;

        let pending_affirms = self.store.row_i64(
            "SELECT pending FROM settlement_pending_affirmations WHERE settlement_ref = ?1",
            params![self.settlement_ref.0.to_vec()],
        )?;
        let pending_affirms = match u32::try_from(pending_affirms) {
            Ok(0) => return Err(ChainFailure::Error(ChainError::NoPendingAffirmations)),
            Ok(v) => v - 1,
            Err(_) => return Err(ChainFailure::Error(ChainError::AmountOverflow)),
        };
        self.store.conn.execute(
            "UPDATE settlement_pending_affirmations SET pending = ?2 WHERE settlement_ref = ?1",
            params![self.settlement_ref.0.to_vec(), pending_affirms as i64],
        )?;

        Ok(PendingCounts {
            affirms: pending_affirms,
            finals: pending_final,
        })
    }

    /// `party_finalizes`.
    pub fn party_finalizes(&self, party: LegAffirmParty) -> ChainResult<u32> {
        self.set_party_status(
            party,
            AffirmationStatus::Affirmed,
            AffirmationStatus::Finalized,
        )
    }

    // -------------------------------------------------- counters

    pub fn pending_affirmations(&self) -> ChainResult<u32> {
        u32::try_from(self.store.row_i64(
            "SELECT pending FROM settlement_pending_affirmations WHERE settlement_ref = ?1",
            params![self.settlement_ref.0.to_vec()],
        )?)
        .map_err(|_| ChainFailure::Error(ChainError::AmountOverflow))
    }

    pub fn pending_finalizations(&self) -> ChainResult<u32> {
        u32::try_from(self.store.row_i64(
            "SELECT pending FROM settlement_pending_finalizations WHERE settlement_ref = ?1",
            params![self.settlement_ref.0.to_vec()],
        )?)
        .map_err(|_| ChainFailure::Error(ChainError::AmountOverflow))
    }

    fn add_pending_finalizations(&self, n: u32) -> ChainResult<u32> {
        let current = self.pending_finalizations()?;
        let new = current.saturating_add(n);
        self.store.conn.execute(
            "INSERT INTO settlement_pending_finalizations (settlement_ref, pending) VALUES (?1, ?2)
             ON CONFLICT(settlement_ref) DO UPDATE SET pending = ?2",
            params![self.settlement_ref.0.to_vec(), new as i64],
        )?;
        Ok(new)
    }

    fn sub_pending_finalizations(&self, n: u32) -> ChainResult<u32> {
        let current = self.pending_finalizations()?;
        let new = current.saturating_sub(n);
        self.store.conn.execute(
            "INSERT INTO settlement_pending_finalizations (settlement_ref, pending) VALUES (?1, ?2)
             ON CONFLICT(settlement_ref) DO UPDATE SET pending = ?2",
            params![self.settlement_ref.0.to_vec(), new as i64],
        )?;
        Ok(new)
    }

    // -------------------------------------------------- transitions

    /// `check_for_execution`.
    pub fn check_for_execution(&self, pending: PendingCounts) -> ChainResult<()> {
        if self.status == SettlementStatus::Pending && pending.affirms == 0 {
            self.execute()?;
            if pending.finals == 0 {
                self.finalize()?;
            }
        }
        Ok(())
    }

    /// `check_for_finalization`.
    pub fn check_for_finalization(&self, pending_final: u32) -> ChainResult<()> {
        if matches!(
            self.status,
            SettlementStatus::Executed | SettlementStatus::Rejected
        ) && pending_final == 0
        {
            self.finalize()?;
        }
        Ok(())
    }

    /// `reject`.
    pub fn reject(&self, pending_finals: u32) -> ChainResult<()> {
        if self.status != SettlementStatus::Pending {
            return Err(ChainFailure::Error(ChainError::SettlementNotPending));
        }
        self.store.conn.execute(
            "DELETE FROM settlement_pending_affirmations WHERE settlement_ref = ?1",
            params![self.settlement_ref.0.to_vec()],
        )?;

        if pending_finals > 0 {
            self.set_status(SettlementStatus::Rejected)
        } else {
            self.finalize()
        }
    }

    /// `execute`.
    pub fn execute(&self) -> ChainResult<()> {
        if self.status != SettlementStatus::Pending {
            return Err(ChainFailure::Error(ChainError::SettlementNotPending));
        }
        self.store.conn.execute(
            "DELETE FROM settlement_pending_affirmations WHERE settlement_ref = ?1",
            params![self.settlement_ref.0.to_vec()],
        )?;
        self.set_status(SettlementStatus::Executed)
    }

    /// `finalize` -> `Pallet::finalize_settlement`: prune everything except the `Finalized`
    /// tombstone, which is the settlement-proof replay guard.
    pub fn finalize(&self) -> ChainResult<()> {
        self.store.finalize_settlement(&self.settlement_ref)?;
        Ok(())
    }

    fn set_status(&self, status: SettlementStatus) -> ChainResult<()> {
        self.store.conn.execute(
            "INSERT INTO settlement_state (settlement_ref, status) VALUES (?1, ?2)
             ON CONFLICT(settlement_ref) DO UPDATE SET status = ?2",
            params![self.settlement_ref.0.to_vec(), status.name()],
        )?;
        self.store.event(
            "SettlementStatusUpdated",
            format!("{} -> {}", self.status.name(), status.name()),
        )?;
        Ok(())
    }
}

impl Store {
    /// `ensure_last_pending_affirmation`: instant affirmations must be the last pending
    /// affirmation for the settlement.
    pub fn ensure_last_pending_affirmation(
        &self,
        settlement_ref: &SettlementRef,
        expected: u32,
    ) -> ChainResult<()> {
        let key = settlement_ref.0.to_vec();
        let pending = u32::try_from(self.row_i64(
            "SELECT pending FROM settlement_pending_affirmations WHERE settlement_ref = ?1",
            params![key],
        )?)
        .map_err(|_| ChainFailure::Error(ChainError::AmountOverflow))?;
        if pending != expected {
            return Err(ChainFailure::Error(ChainError::NotLastPendingAffirmation));
        }
        Ok(())
    }

    /// `ensure_settlement_executed` (pallet `lib.rs:3209`).
    pub fn ensure_settlement_executed(&self, settlement_ref: &SettlementRef) -> ChainResult<()> {
        let status = self
            .row_text(
                "SELECT status FROM settlement_state WHERE settlement_ref = ?1",
                params![settlement_ref.0.to_vec()],
            )?
            .map(|s| SettlementStatus::from_name(&s))
            .transpose()?
            .ok_or(ChainFailure::Error(ChainError::SettlementNotFound))?;
        if status != SettlementStatus::Executed {
            return Err(ChainFailure::Error(ChainError::SettlementNotExecuted));
        }
        Ok(())
    }

    /// `finalizing_leg_count`: the optional per-proof leg count must match the stored one.
    pub fn finalizing_leg_count(
        &self,
        settlement_ref: &SettlementRef,
        legs: Option<u8>,
    ) -> ChainResult<(SettlementRef, u32)> {
        let key = settlement_ref.0.to_vec();
        let leg_count = u32::try_from(self.row_i64(
            "SELECT leg_count FROM settlement_leg_count WHERE settlement_ref = ?1",
            params![key],
        )?)
        .map_err(|_| ChainFailure::Error(ChainError::LegNotFound))?;
        if let Some(legs) = legs {
            if u32::from(legs) != leg_count {
                return Err(ChainFailure::Error(ChainError::SettlementLegCountMismatch));
            }
        }
        Ok((
            SettlementRef(
                key.try_into()
                    .map_err(|_| ChainFailure::Internal("bad settlement ref".into()))?,
            ),
            leg_count,
        ))
    }

    /// `finalize_settlement`: prune all settlement storage except the `Finalized` tombstone.
    pub fn finalize_settlement(&self, settlement_ref: &SettlementRef) -> ChainResult<()> {
        let key = settlement_ref.0.to_vec();
        for table in [
            "settlement_pending_finalizations",
            "settlement_pending_affirmations",
            "settlement_memo",
        ] {
            self.conn.execute(
                &format!("DELETE FROM {table} WHERE settlement_ref = ?1",),
                params![key],
            )?;
        }

        let leg_count = u32::try_from(self.row_i64(
            "SELECT leg_count FROM settlement_leg_count WHERE settlement_ref = ?1",
            params![key],
        )?)
        .unwrap_or(0);
        for leg_id in 0..leg_count {
            self.conn.execute(
                "DELETE FROM leg_affirmation_status WHERE settlement_ref = ?1 AND leg_id = ?2",
                params![key, leg_id as i64],
            )?;
            self.conn.execute(
                "DELETE FROM settlement_legs WHERE settlement_ref = ?1 AND leg_id = ?2",
                params![key, leg_id as i64],
            )?;
            self.conn.execute(
                "DELETE FROM leg_mediators WHERE settlement_ref = ?1 AND leg_id = ?2",
                params![key, leg_id as i64],
            )?;
        }
        self.conn.execute(
            "DELETE FROM settlement_leg_count WHERE settlement_ref = ?1",
            params![key],
        )?;

        self.conn.execute(
            "INSERT INTO settlement_state (settlement_ref, status) VALUES (?1, 'Finalized')
             ON CONFLICT(settlement_ref) DO UPDATE SET status = 'Finalized'",
            params![key],
        )?;
        self.event(
            "SettlementStatusUpdated",
            format!("{settlement_ref} -> Finalized"),
        )?;
        Ok(())
    }
}
