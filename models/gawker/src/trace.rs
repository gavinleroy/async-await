use serde_json::{Map, Value};

pub struct TraceEvent {
    pub event_type: String,
    pub seq: u64,
    pub ts: f64,
    pub tid: u64,
    pub fields: Map<String, Value>,
}

impl TraceEvent {
    pub fn from_value(value: Value) -> Option<Self> {
        let obj = value.as_object()?;
        Some(TraceEvent {
            event_type: obj.get("type")?.as_str()?.to_string(),
            seq: obj.get("seq")?.as_u64()?,
            ts: obj.get("ts")?.as_f64()?,
            tid: obj.get("tid")?.as_u64()?,
            fields: obj.clone(),
        })
    }

    pub fn get_str(&self, key: &str) -> Option<&str> {
        self.fields.get(key)?.as_str()
    }

    pub fn get_u64(&self, key: &str) -> Option<u64> {
        self.fields.get(key)?.as_u64()
    }

    pub fn get_f64(&self, key: &str) -> Option<f64> {
        self.fields.get(key)?.as_f64()
    }

    pub fn get_bool(&self, key: &str) -> Option<bool> {
        self.fields.get(key)?.as_bool()
    }

    pub fn summary(&self) -> String {
        let task = self
            .get_u64("task-id")
            .map(|id| format!("task:{id}"))
            .unwrap_or_default();

        match self.event_type.as_str() {
            "runtime:startup" => {
                let eager = self.get_str("eagerness").unwrap_or("?");
                let pool = self.get_u64("pool-size").unwrap_or(0);
                format!("pool={pool} eagerness={eager}")
            }
            "task:create" => {
                let parent = self
                    .get_u64("parent-id")
                    .map(|id| format!("parent:{id}"))
                    .unwrap_or_else(|| "root".into());
                format!("{task} {parent}")
            }
            "sched:enqueue" => task,
            "sched:dispatch" => {
                let outcome = self.get_str("outcome").unwrap_or("?");
                format!("{task} \u{2192} {outcome}")
            }
            "sched:thread-acquired" => {
                let w = self.get_u64("worker-tid").unwrap_or(0);
                format!("worker:{w} {task}")
            }
            "sched:thread-released" => {
                let w = self.get_u64("worker-tid").unwrap_or(0);
                format!("worker:{w}")
            }
            "coro:resume" => {
                let kind = self.get_str("resume-kind").unwrap_or("?");
                format!("{task} {kind}")
            }
            "coro:suspended" | "coro:completed" => {
                let stdout = self.get_str("stdout").unwrap_or("");
                if stdout.is_empty() {
                    task
                } else {
                    format!("{task} stdout={stdout:?}")
                }
            }
            "coro:failed" => {
                let err = self.get_str("error").unwrap_or("?");
                format!("{task} {err}")
            }
            "cancel:mark" => task,
            "cancel:request" => {
                let target = self.get_u64("target-id").unwrap_or(0);
                format!("target:{target}")
            }
            "cancel:propagate" => {
                let p = self.get_u64("parent-id").unwrap_or(0);
                let c = self.get_u64("child-id").unwrap_or(0);
                format!("task:{p} \u{2192} task:{c}")
            }
            "task:settled" => {
                let status = self.get_str("status").unwrap_or("?");
                format!("{task} {status}")
            }
            "task:terminated" | "task:waiting-children" => task,
            "task:body-done" => {
                let failed = self.get_bool("failed").unwrap_or(false);
                let children = self.get_u64("pending-children").unwrap_or(0);
                format!("{task} failed={failed} children={children}")
            }
            "task:destruct" => {
                let d = self.get_str("destruction").unwrap_or("?");
                format!("{task} {d}")
            }
            "promise:create" => {
                let p = self.get_u64("promise-id").unwrap_or(0);
                format!("promise:{p}")
            }
            "promise:fulfil" => {
                let p = self.get_u64("promise-id").unwrap_or(0);
                let cbs = self.get_u64("callback-count").unwrap_or(0);
                format!("promise:{p} callbacks={cbs}")
            }
            "io:timer-register" => {
                let p = self.get_u64("promise-id").unwrap_or(0);
                let ms = self.get_u64("delay-ms").unwrap_or(0);
                format!("{task} promise:{p} +{ms}ms")
            }
            "io:timer-fired" | "io:timer-cancelled" => {
                let p = self.get_u64("promise-id").unwrap_or(0);
                format!("promise:{p}")
            }
            "io:timer-registered" => {
                let p = self.get_u64("promise-id").unwrap_or(0);
                let n = self.get_u64("pending-timers").unwrap_or(0);
                format!("promise:{p} total={n}")
            }
            "await:inline-splice" | "await:fast-path" | "await:suspend" => task,
            "spawn:task" => {
                let parent = self
                    .get_u64("parent-id")
                    .map(|id| format!("parent:{id}"))
                    .unwrap_or_else(|| "root".into());
                format!("{task} {parent}")
            }
            "spawn:existing" => task,
            "runtime:block-on" => task,
            "runtime:block-on-exit" => {
                let st = self.get_str("state").unwrap_or("?");
                format!("{task} {st}")
            }
            "runtime:shutdown" | "runtime:all-settled" => String::new(),
            _ => String::new(),
        }
    }
}

pub fn load_trace(path: &str) -> Vec<TraceEvent> {
    let content = std::fs::read_to_string(path).expect("failed to read trace file");
    let mut events: Vec<TraceEvent> = content
        .lines()
        .filter(|line| !line.trim().is_empty())
        .filter_map(|line| {
            let value: Value = serde_json::from_str(line).ok()?;
            TraceEvent::from_value(value)
        })
        .collect();
    events.sort_by(|a, b| a.ts.partial_cmp(&b.ts).unwrap_or(std::cmp::Ordering::Equal));
    events
}
