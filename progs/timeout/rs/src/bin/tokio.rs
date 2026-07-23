use std::time::Duration;
use tokio::{select, time::sleep};
use tokio_util::sync::CancellationToken;

async fn timeout<T>(duration: Duration, task: impl Future<Output = T>) -> Option<T> {
  select! {
    result = task => Some(result),
    _ = sleep(duration) => None,
  }
}

async fn timeout_task<T, Fut>(duration: Duration, task: Fut) -> Option<T>
where
  T: Send + 'static,
  Fut: Future<Output = T> + Send + 'static,
{
  let mut handle = tokio::spawn(task);
  select! {
    result = &mut handle => Some(result.unwrap()),
    _ = sleep(duration) => {
      handle.abort();
      None
    },
  }
}

#[derive(Debug)]
enum TimeoutResult<T> {
  Success(T),
  TimedOut,
  Cancelled,
}

async fn timeout_cancellable<T, Fut>(
  duration: Duration,
  token: CancellationToken,
  f: impl Fn(CancellationToken) -> Fut,
) -> TimeoutResult<T>
where
  T: Send + 'static,
  Fut: Future<Output = T> + Send + 'static,
{
  let mut handle = tokio::spawn(f(token.child_token()));
  select! {
    result = &mut handle => TimeoutResult::Success(result.unwrap()),
    _ = token.cancelled() => TimeoutResult::Cancelled,
    _ = sleep(duration) => {
      token.cancel();
      TimeoutResult::TimedOut
    }
  }
}

#[tokio::main]
async fn main() {
  println!(
    "{:#?}",
    timeout(Duration::from_secs(1), sleep(Duration::from_secs(2))).await
  );

  println!(
    "{:#?}",
    timeout_task(Duration::from_secs(1), sleep(Duration::from_secs(2))).await
  );

  let token = CancellationToken::new();
  println!(
    "{:#?}",
    timeout_cancellable(Duration::from_secs(1), token, async |token| {
      select! {
        _ = sleep(Duration::from_secs(2)) => {
          println!("Yo!");
        }
        _ = token.cancelled() => {
          println!("Cancelled :(");
        }
      }
    })
    .await
  );

  let token = CancellationToken::new();
  let child = token.child_token();
  let handle = tokio::spawn(timeout_cancellable(
    Duration::from_secs(5),
    child,
    async |token| {
      select! {
        _ = sleep(Duration::from_secs(2)) => {
          println!("Yo!");
        }
        _ = token.cancelled() => {
          println!("Cancelled :(");
        }
      }
    },
  ));
  token.cancel();
  println!("{:#?}", handle.await.unwrap());
}
