use std::time::Duration;

async fn asyncf() {
    println!("async running");
}

async fn wrapper() {
    let coro = asyncf();

    tokio::time::sleep(Duration::from_secs(1)).await;
    println!("wrapper running");
    coro.await;
}

#[tokio::main]
async fn main() {
    let () = wrapper().await;
}
