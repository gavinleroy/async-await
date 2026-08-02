// Figure 1-dev — Rust + tokio (decision-tree variant).
//
// Three calling contexts, one per dimension group:
//   ex1 START OF LIFE  plain async application, never polled
//   ex2 END OF LIFE    spawn detached, extent ends un-awaited
//   ex3 CANCELLATION   timeout a parent awaiting its spawned child
//
// spawn      = tokio::spawn (indefinite extent; the task keeps running
//              when its JoinHandle is dropped)
// timeout    = figlib::timeout: on expiry the future is DROPPED (Rust
//              cancellation-by-drop)
//
// Predicted: ex1 `C` (lazy: the future is never polled), ex2 `AC`
// (strong: the dropped JoinHandle detaches the task, which runs until
// runtime shutdown kills it mid-sleep), ex3 `ACB` (the timeout drops the
// parent at 1 s, but dropping the held JoinHandle DETACHES the child,
// which completes during the grace).

mod figlib;

use figlib::{sleep, timeout};

async fn write_to_log() {
    println!("A");
    // simulate log write
    sleep(2).await;
    println!("B");
}

async fn process_await() {
    let task = tokio::spawn(write_to_log());
    sleep(0).await;
    let _ = task.await;
}

async fn process_detached() {
    let _task = tokio::spawn(write_to_log());
    // handle drops at return: the task detaches
}

async fn ex1() {
    let _t = write_to_log(); // plain application: a future, never polled
    println!("C");
    sleep(3).await;
}

async fn ex2() {
    process_detached().await;
    sleep(1).await;
    println!("C");
    // extent ends: runtime shutdown drops the task mid-sleep
}

async fn ex3() {
    timeout(1, process_await()).await;
    println!("C");
    sleep(3).await;
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
