use tokio::task::JoinSet;

async fn wait_n<T, F>(futs: impl Iterator<Item = F>) -> Vec<T>
where
    T: Send + 'static,
    F: Future<Output = T> + Send + 'static,
{
    JoinSet::from_iter(futs).join_all().await
}

#[tokio::main]
async fn main() {
    let timer = std::time::Instant::now();
    let futs = (0..=1000).map(std::future::ready);
    let ns = wait_n(futs).await;
    let res: usize = ns.iter().sum();
    assert_eq!(res, 500500);
    println!("done {}μs", timer.elapsed().as_micros());
}
