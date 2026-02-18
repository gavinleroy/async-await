use tokio::task::JoinSet;

async fn race_n<T, F>(futs: impl Iterator<Item = F>) -> Option<T>
where
    T: Send + 'static,
    F: Future<Output = T> + Send + 'static,
{
    let Some(Ok(result)) = JoinSet::from_iter(futs).join_next().await else {
        return None;
    };

    Some(result)
}

#[tokio::main]
async fn main() {
    let n = 42;
    let timer = std::time::Instant::now();
    let futs = (0..=1000).map(|i| async move {
        if i == n {
            i
        } else {
            std::future::pending::<usize>().await
        }
    });

    let res = race_n(futs).await;
    assert_eq!(res, Some(n));
    println!("done {}μs", timer.elapsed().as_micros());
}
