// Figure 1 — Rust + tokio (timeout variant).
//
// spawn      = tokio::spawn (indefinite extent; the task keeps running
//              when its JoinHandle is dropped)
// timeout    = figlib::timeout: tokio's built-in — drops the future on
//              expiry (cancellation-by-drop); tasks IT spawned keep
//              running detached
// isolation  = ONE #[tokio::main] runtime for all three exs; each ex ends
//              with a 3 s grace sleep, so detached work completes inside
//              its own ex's section.
//
// Predicted: ex1 `AB` (the grace keeps the runtime alive past the detached
// task's sleep), ex2 `AB` (the timeout drops process_await at 1 s, but
// the inner spawned task runs detached to completion), ex3 `AB` (same).

mod figlib;

use figlib::{sleep, timeout};

fn grace() -> u64 {
    std::env::var("GRACE")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(3)
}

async fn write_to_log() {
    println!("A");
    // simulate log write
    sleep(2).await;
    println!("B");
}

async fn process_await() {
    let task = tokio::spawn(write_to_log()); // spawn
    sleep(0).await; // do other work ...
    let _ = task.await;
}

async fn process_detach() {
    tokio::spawn(write_to_log()); // spawn, handle dropped, task keeps running
    sleep(0).await; // do other work ...
}

async fn ex1() {
    process_detach().await;
}

async fn ex2() {
    timeout(1, process_await()).await;
}

async fn ex3() {
    timeout(1, process_detach()).await;
}

#[tokio::main]
async fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("1") => ex1().await,
        Some("2") => ex2().await,
        Some("3") => ex3().await,
        _ => panic!("expected ex number 1-3"),
    }
    sleep(grace()).await;
}
