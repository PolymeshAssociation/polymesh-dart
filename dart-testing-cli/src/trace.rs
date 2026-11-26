//! Trace of simulated dispatches and events.
//!
//! Every simulated extrinsic records one `tx_log` row (the dispatch outcome) and any pallet events
//! it emits, so a security review can replay what the chain actually did and assert that the CLI
//! rejected the same thing the pallet would.
//!
//! Events are buffered during a dispatch because the pallet only emits them if the extrinsic
//! succeeds: when the dispatch fails, storage changes *and* events are rolled back. `flush` writes
//! the trace after the transaction ends, so the trace survives rollbacks while the chain state does
//! not.

use rusqlite::{params, OptionalExtension};

use crate::config::Moment;
use crate::errors::ChainResult;
use crate::storage::Store;

#[derive(Debug, Clone)]
pub struct Trace {
    pub id: i64,
    pub block: u32,
    pub moment: Moment,
    pub call: String,
    pub outcome: String,
    pub error: Option<String>,
    /// Events emitted by this dispatch. `Detail` rows are CLI annotations, not pallet events.
    pub events: Vec<(String, String)>,
}

impl Store {
    /// Buffer a pallet event (`Self::deposit_event`) for the dispatch in progress.
    pub fn event(&self, event: &str, detail: String) -> ChainResult<()> {
        self.pending_events
            .borrow_mut()
            .push((event.to_string(), detail));
        Ok(())
    }

    /// Write the trace for the dispatch that just finished. On failure the buffered events are
    /// dropped (the pallet emits nothing for a failed extrinsic) and only the diagnostic lines are
    /// recorded.
    pub fn flush_trace(
        &self,
        call: &str,
        error: Option<&str>,
        diagnostics: impl IntoIterator<Item = String>,
    ) -> ChainResult<()> {
        let buffered = self.pending_events.take();
        let block = self.block_number()?;
        let moment = self.timestamp()?;
        let outcome = if error.is_some() { "Error" } else { "Ok" };
        self.conn.execute(
            "INSERT INTO tx_log (block_number, moment, call, outcome, error) VALUES (?1, ?2, ?3, ?4, ?5)",
            params![block as i64, moment as i64, call, outcome, error],
        )?;
        let id = self.conn.last_insert_rowid();

        let rows: Vec<(String, String)> = if error.is_some() {
            diagnostics
                .into_iter()
                .map(|d| ("Detail".to_string(), d))
                .collect()
        } else {
            buffered
        };
        for (event, detail) in rows {
            self.conn.execute(
                "INSERT INTO event_log (tx_id, block_number, call, event, detail) VALUES (?1, ?2, ?3, ?4, ?5)",
                params![id, block as i64, call, event, detail],
            )?;
        }
        Ok(())
    }

    /// Attach events buffered *after* a dispatch (e.g. the `RelayerBatchedProofs` event emitted
    /// at the end of a multi-transaction extrinsic) to the most recent `tx_log` row. Without
    /// this, the event would be dropped at process exit or misattributed to the next dispatch.
    pub fn flush_pending_events(&self) -> ChainResult<()> {
        let buffered = self.pending_events.take();
        if buffered.is_empty() {
            return Ok(());
        }
        let tx_id: Option<i64> = self
            .conn
            .query_row("SELECT MAX(id) FROM tx_log", [], |row| row.get(0))
            .optional()?
            .flatten();
        let Some(tx_id) = tx_id else {
            return Ok(());
        };
        let (block, call): (i64, String) = self.conn.query_row(
            "SELECT block_number, call FROM tx_log WHERE id = ?1",
            params![tx_id],
            |row| Ok((row.get(0)?, row.get(1)?)),
        )?;
        for (event, detail) in buffered {
            self.conn.execute(
                "INSERT INTO event_log (tx_id, block_number, call, event, detail) VALUES (?1, ?2, ?3, ?4, ?5)",
                params![tx_id, block, call, event, detail],
            )?;
        }
        Ok(())
    }

    /// All recorded dispatches with their events, in execution order.
    pub fn read_trace(&self) -> ChainResult<Vec<Trace>> {
        let mut traces = {
            let mut stmt = self.conn.prepare(
                "SELECT id, block_number, moment, call, outcome, error FROM tx_log ORDER BY id",
            )?;
            let rows = stmt.query_map([], |row| {
                Ok(Trace {
                    id: row.get(0)?,
                    block: row.get::<_, i64>(1)? as u32,
                    moment: row.get::<_, i64>(2)? as u64,
                    call: row.get(3)?,
                    outcome: row.get(4)?,
                    error: row.get(5)?,
                    events: Vec::new(),
                })
            })?;
            let mut out = Vec::new();
            for row in rows {
                out.push(row?);
            }
            out
        };
        let mut stmt = self
            .conn
            .prepare("SELECT tx_id, event, detail FROM event_log ORDER BY id")?;
        let events: Vec<(i64, String, String)> = stmt
            .query_map([], |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)))?
            .collect::<Result<Vec<_>, _>>()?;
        for trace in traces.iter_mut() {
            for (tx_id, event, detail) in &events {
                if *tx_id == trace.id {
                    trace.events.push((event.clone(), detail.clone()));
                }
            }
        }
        Ok(traces)
    }
}
