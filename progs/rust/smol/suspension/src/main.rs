use std::time::Duration;

//Suspension: Dynamic
async fn print(msg: &str) {
    println!("{msg}");
    smol::Timer::after(Duration::from_millis(0)).await;
}

async fn work(name: &str) {
    print(name).await;
    print(name).await;
    print(name).await;
}

// NOTE, SMOL's default executor is single threaded
fn main() {
    smol::block_on(async {
        let a = smol::spawn(work("A"));
        let b = smol::spawn(work("B"));
        print("C").await;
        a.await;
        b.await;
    })
}
