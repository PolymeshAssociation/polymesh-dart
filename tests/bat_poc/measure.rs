//! Timing and markdown output.
//!
//! Median of `iters` with one discarded warmup, matching how `perf_comparison_results_1.md` was
//! produced. Not criterion: the configuration matrix is large and what is wanted is one table per
//! curve, not a statistical report per cell.

use std::{hint::black_box, time::Duration, time::Instant};

pub fn bench<T>(iters: usize, mut f: impl FnMut() -> T) -> Duration {
    black_box(f());
    let mut samples = Vec::with_capacity(iters);
    for _ in 0..iters {
        let start = Instant::now();
        let out = f();
        samples.push(start.elapsed());
        black_box(out);
    }
    samples.sort_unstable();
    samples[samples.len() / 2]
}

pub fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

pub fn fmt_ms(d: Duration) -> String {
    let v = ms(d);
    if v < 0.01 {
        format!("{:.4}", v)
    } else if v < 10.0 {
        format!("{:.3}", v)
    } else {
        format!("{:.1}", v)
    }
}

pub struct Table {
    header: Vec<String>,
    rows: Vec<Vec<String>>,
}

impl Table {
    pub fn new(header: &[&str]) -> Self {
        Self {
            header: header.iter().map(|s| s.to_string()).collect(),
            rows: Vec::new(),
        }
    }

    pub fn row(&mut self, cells: Vec<String>) {
        assert_eq!(cells.len(), self.header.len());
        self.rows.push(cells);
    }

    pub fn print(&self, title: &str) {
        let mut w: Vec<usize> = self.header.iter().map(|h| h.len()).collect();
        for r in &self.rows {
            for (i, c) in r.iter().enumerate() {
                w[i] = w[i].max(c.len());
            }
        }
        println!("\n### {title}\n");
        let line = |cells: &[String]| {
            let inner: Vec<String> = cells
                .iter()
                .enumerate()
                .map(|(i, c)| format!(" {:<width$} ", c, width = w[i]))
                .collect();
            format!("|{}|", inner.join("|"))
        };
        println!("{}", line(&self.header));
        let sep: Vec<String> = w.iter().map(|n| "-".repeat(*n)).collect();
        println!("{}", line(&sep));
        for r in &self.rows {
            println!("{}", line(r));
        }
    }
}
