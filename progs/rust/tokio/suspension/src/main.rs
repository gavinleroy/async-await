//Suspension: Dynamic
use std::{
    fmt::Display,
    sync::atomic::{AtomicUsize, Ordering},
};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

async fn r#continue() -> bool {
    true
}

async fn write<T: AsRef<str> + Display + Sized>(msg: T) {
    print!("{msg}");
}

async fn async_int() -> i32 {
    let me = COUNTER.fetch_add(1, Ordering::SeqCst);
    let until = rand::random_range(0..5000);

    for _ in 0..until {
        if !r#continue().await {
            break;
        }
        write(format!("{me}")).await;
    }
    write(format!("{me} done")).await;

    until
}

// NOTE, with a single threaded runtime we see that the 0's all get
// printed before the 1's because the thread never yields
#[tokio::main(flavor = "current_thread")]
async fn main() {
    let a = tokio::spawn(async_int());
    let b = tokio::spawn(async_int());
    println!("working");
    let c = a.await.unwrap() + b.await.unwrap();
    write(c.to_string()).await;
}
