//Exn: awaited (for results, panics are just logged)
use std::{fmt::Display, time::Duration};

async fn write<T: AsRef<str> + Display + Sized>(msg: T) {
    println!("{}", msg);
    smol::Timer::after(Duration::from_millis(5)).await;
}

async fn async_int() -> i32 {
    let inner = async || panic!("argh");
    // NOTE, if you change this to an `await` then the main program will exit with 101
    smol::spawn(inner()).detach();
    0
}

// NOTE, the panic is printed in the thread but the exit status is still 0
fn main() {
    smol::block_on(async {
        let a = async_int();
        let b = async_int();
        println!("working");
        let c = a.await + b.await;
        write(c.to_string()).await;
    })
}
