// Figure 1-dev — Rust + tokio (decision-tree variant).
//
// Three calling contexts, one per dimension group:
//   ex1 START OF LIFE  plain async application, never polled
//   ex2 END OF LIFE    spawn, extent ends un-awaited (no grace)
//   ex3 CANCELLATION   timeout a parent awaiting its spawned child
//
// spawn      = tokio::spawn (indefinite extent; the task keeps running
//              when its JoinHandle is dropped)
// timeout    = figlib::timeout: on expiry the future is DROPPED (Rust
//              cancellation-by-drop)
//
// Predicted: ex1 `C` (lazy: the future is never polled), ex2 `AC`
// (strong: the dropped JoinHandle detaches the task, which runs until
// runtime shutdown kills it mid-sleep), ex3 `AB` (the timeout drops the
// parent, but dropping the held JoinHandle DETACHES the child, which
// completes during the grace).

mod figlib;

use figlib::{sleep, timeout};

fn grace() -> u64 {
    std::env::var("GRACE")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(3)
}

async fn work(d: u64) {
    println!("A");
    // simulate log write
    sleep(d).await;
    println!("B");
}

async fn ex1() {
    let _t = work(0); // plain application: a future, never polled
    println!("C");
    sleep(grace()).await;
}

async fn ex2() {
    let _ = tokio::spawn(work(2)); // spawn, handle dropped: task detaches
    sleep(1).await; // do other work ...
    println!("C");
    // extent ends: runtime shutdown drops the task mid-sleep
}

async fn parent() {
    let task = tokio::spawn(work(2));
    let _ = task.await;
}

async fn ex3() {
    timeout(1, parent()).await;
    sleep(grace()).await;
}

#[tokio::main]
async fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("1") => ex1().await,
        Some("2") => ex2().await,
        Some("3") => ex3().await,
        _ => panic!("expected ex number 1-3"),
    }
}
