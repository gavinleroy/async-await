// Figure 1-dev — Rust + smol (decision-tree variant).
//
// Three calling contexts, one per dimension group:
//   ex1 START OF LIFE  plain async application, never polled
//   ex2 END OF LIFE    spawn, extent ends un-awaited (no grace)
//   ex3 CANCELLATION   timeout a parent awaiting its spawned child
//
// spawn      = smol::spawn on the global executor; smol tasks CANCEL when
//              their handle drops (the weak-reference design)
// timeout    = figlib::timeout: on expiry the future is DROPPED (Rust
//              cancellation-by-drop); a Task handle held inside cancels
//              its task
//
// Predicted: ex1 `C` (lazy: the future is never polled), ex2 `C` (weak:
// the spawn's handle drops immediately, closing the task before its
// first poll — not even A prints), ex3 `A` (the timeout drops the
// parent; dropping its held handle cancels the child mid-sleep).

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
    let _ = smol::spawn(work(2)); // spawn, handle dropped: task cancelled
    sleep(1).await; // do other work ...
    println!("C");
}

async fn parent() {
    let task = smol::spawn(work(2));
    task.await;
}

async fn ex3() {
    timeout(1, parent()).await;
    sleep(grace()).await;
}

fn main() {
    smol::block_on(async {
        match std::env::args().nth(1).as_deref() {
            Some("1") => ex1().await,
            Some("2") => ex2().await,
            Some("3") => ex3().await,
            _ => panic!("expected ex number 1-3"),
        }
    });
}
