use ratatui::{
    Frame,
    layout::{Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Paragraph, Wrap},
};
use serde_json::Value;

use crate::app::{App, Panel};
use crate::state::{RuntimeState, TaskStatus};

pub fn render(frame: &mut Frame, app: &mut App) {
    let outer = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Percentage(40),
            Constraint::Min(5),
            Constraint::Length(1),
        ])
        .split(frame.area());

    render_events(frame, app, outer[0]);

    let bottom = Layout::default()
        .direction(Direction::Horizontal)
        .constraints([Constraint::Percentage(40), Constraint::Percentage(60)])
        .split(outer[1]);

    let left_col = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Percentage(40),
            Constraint::Percentage(20),
            Constraint::Percentage(20),
            Constraint::Percentage(20),
        ])
        .split(bottom[0]);

    let right_col = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Percentage(50), Constraint::Percentage(50)])
        .split(bottom[1]);

    app.panel_areas.events = Some(outer[0]);
    app.panel_areas.tasks = Some(left_col[0]);
    app.panel_areas.source = Some(right_col[0]);
    app.panel_areas.detail = Some(right_col[1]);

    render_task_tree(frame, app, left_col[0]);
    render_task_queue(frame, app, left_col[1]);
    render_io(frame, app, left_col[2]);
    render_output(frame, app, left_col[3]);
    render_source(frame, app, right_col[0]);
    render_detail(frame, app, right_col[1]);
    render_status_bar(frame, app, outer[2]);
}

fn border_style(app: &App, panel: Panel) -> Style {
    if app.focus == panel {
        Style::default().fg(Color::Cyan)
    } else {
        Style::default().fg(Color::DarkGray)
    }
}

fn event_type_color(event_type: &str) -> Color {
    match event_type.split(':').next().unwrap_or("") {
        "task" | "spawn" => Color::Blue,
        "sched" => Color::Yellow,
        "coro" | "await" => Color::Green,
        "cancel" => Color::Red,
        "io" | "promise" => Color::Cyan,
        "runtime" => Color::Magenta,
        _ => Color::White,
    }
}

fn render_events(frame: &mut Frame, app: &mut App, area: Rect) {
    let block = Block::bordered()
        .title(" Events ")
        .border_style(border_style(app, Panel::Events));
    let inner = block.inner(area);
    frame.render_widget(block, area);

    if app.events.is_empty() || inner.width == 0 || inner.height < 2 {
        return;
    }

    let n_cols = app.thread_columns.len().max(1);
    let col_w = (inner.width as usize) / n_cols;
    if col_w < 6 {
        return;
    }

    let buf = frame.buffer_mut();
    let dim = Style::default().fg(Color::DarkGray);

    // Header row
    for ci in 0..n_cols {
        let x = inner.x + (ci * col_w) as u16;
        if ci > 0 {
            buf.set_string(x, inner.y, "\u{2502}", dim);
        }
        let offset: u16 = if ci > 0 { 1 } else { 0 };
        let tid = app.thread_columns[ci];
        let name = app
            .thread_labels
            .get(&tid)
            .map(|s| s.as_str())
            .unwrap_or("?");
        let label = format!(" {name}");
        let trunc: String = label.chars().take(col_w - offset as usize).collect();
        buf.set_string(
            x + offset,
            inner.y,
            &trunc,
            Style::default().fg(Color::Cyan).add_modifier(Modifier::DIM),
        );
    }

    // Event rows
    let vis_h = (inner.height as usize).saturating_sub(1);
    if vis_h == 0 {
        return;
    }
    let scroll = centered_scroll(app.cursor, vis_h, app.events.len());

    let busy_bg = Color::Rgb(30, 30, 35);

    for (row, ev_i) in (scroll..).enumerate().take(vis_h) {
        if ev_i >= app.events.len() {
            break;
        }
        let event = &app.events[ev_i];
        let ev_col = app
            .thread_columns
            .iter()
            .position(|&t| t == event.tid)
            .unwrap_or(0);
        let y = inner.y + 1 + row as u16;
        let is_cur = ev_i == app.cursor;
        let row_state = &app.states[ev_i + 1];

        // Busy-thread background shading
        for ci in 0..n_cols {
            let tid = app.thread_columns[ci];
            let is_busy = row_state
                .threads
                .get(&tid)
                .map_or(false, |t| t.current_task.is_some());
            if is_busy && !(is_cur && ci == ev_col) {
                let col_x = inner.x + (ci * col_w) as u16;
                let col_offset: u16 = if ci > 0 { 1 } else { 0 };
                let w = col_w.saturating_sub(col_offset as usize);
                let fill: String = " ".repeat(w);
                buf.set_string(
                    col_x + col_offset,
                    y,
                    &fill,
                    Style::default().bg(busy_bg),
                );
            }
        }

        // Column separators
        for ci in 1..n_cols {
            let sx = inner.x + (ci * col_w) as u16;
            if sx < inner.x + inner.width {
                buf.set_string(sx, y, "\u{2502}", dim);
            }
        }

        // Event content in its column
        let x = inner.x + (ev_col * col_w) as u16;
        let offset: u16 = if ev_col > 0 { 1 } else { 0 };
        let content_x = x + offset;
        let avail = col_w.saturating_sub(offset as usize);

        let col_busy = row_state
            .threads
            .get(&event.tid)
            .map_or(false, |t| t.current_task.is_some());
        let bg = if is_cur {
            Color::DarkGray
        } else if col_busy {
            busy_bg
        } else {
            Color::Reset
        };

        if is_cur {
            let fill: String = " ".repeat(avail);
            buf.set_string(content_x, y, &fill, Style::default().bg(bg));
        }

        let seq_s = format!("{:>3} ", event.seq);
        let seq_len = seq_s.len().min(avail);
        let seq_trunc: String = seq_s.chars().take(avail).collect();
        buf.set_string(
            content_x,
            y,
            &seq_trunc,
            Style::default()
                .fg(if is_cur { Color::White } else { Color::DarkGray })
                .bg(bg),
        );

        let type_avail = avail.saturating_sub(seq_len);
        if type_avail > 0 {
            let etype = event
                .event_type
                .split(':')
                .nth(1)
                .unwrap_or(&event.event_type);
            let type_trunc: String = etype.chars().take(type_avail).collect();
            let mut sty = Style::default()
                .fg(event_type_color(&event.event_type))
                .bg(bg);
            if is_cur {
                sty = sty.add_modifier(Modifier::BOLD);
            }
            buf.set_string(content_x + seq_len as u16, y, &type_trunc, sty);
        }
    }
}

fn centered_scroll(cursor: usize, viewport: usize, total: usize) -> usize {
    if viewport >= total {
        return 0;
    }
    if cursor < viewport / 2 {
        0
    } else if cursor + viewport / 2 >= total {
        total.saturating_sub(viewport)
    } else {
        cursor - viewport / 2
    }
}

fn render_task_tree(frame: &mut Frame, app: &App, area: Rect) {
    let block = Block::bordered()
        .title(" Tasks ")
        .border_style(border_style(app, Panel::Tasks));

    let state = app.current_state();
    let mut lines: Vec<Line> = Vec::new();
    let roots = state.root_tasks();

    if roots.is_empty() {
        let p = Paragraph::new("  (no tasks)")
            .block(block)
            .style(Style::default().fg(Color::DarkGray));
        frame.render_widget(p, area);
        return;
    }

    for (ri, &root_id) in roots.iter().enumerate() {
        let is_last_root = ri == roots.len() - 1;
        collect_task_lines(state, root_id, 0, is_last_root, &mut lines);
    }

    let p = Paragraph::new(lines)
        .block(block)
        .scroll((app.task_scroll as u16, 0));
    frame.render_widget(p, area);
}

fn status_style(status: TaskStatus) -> (Color, &'static str) {
    match status {
        TaskStatus::Pending => (Color::Yellow, "\u{25cb}"),
        TaskStatus::Running => (Color::Blue, "\u{25cf}"),
        TaskStatus::Suspended => (Color::Cyan, "\u{25cb}"),
        TaskStatus::Completed => (Color::Green, "\u{25cf}"),
        TaskStatus::Failed => (Color::Red, "\u{25cf}"),
        TaskStatus::Terminated => (Color::DarkGray, "\u{25cb}"),
    }
}

fn collect_task_lines(
    state: &RuntimeState,
    id: u64,
    depth: usize,
    is_last: bool,
    lines: &mut Vec<Line>,
) {
    let Some(task) = state.tasks.get(&id) else {
        return;
    };

    let (color, icon) = status_style(task.status);
    let is_executing = state.executing_task == Some(id);

    let mut indent = String::new();
    if depth > 0 {
        indent.push_str(&"  ".repeat(depth - 1));
        if is_last {
            indent.push_str("\u{2514}\u{2500}");
        } else {
            indent.push_str("\u{251c}\u{2500}");
        }
    }

    let label_str = task
        .label
        .as_deref()
        .map(|l| format!(" {l}"))
        .unwrap_or_default();
    let cancelled = if task.cancelled { " \u{2715}" } else { "" };

    let exec_marker = if is_executing { "\u{25b6} " } else { "" };

    let bg = if is_executing {
        Color::Rgb(40, 40, 60)
    } else {
        Color::Reset
    };

    let dep_annotation = if let Some(&awaited_tid) = state.await_deps.get(&id) {
        let awaited_label = state
            .tasks
            .get(&awaited_tid)
            .and_then(|t| t.label.as_deref())
            .unwrap_or("");
        if awaited_label.is_empty() {
            format!(" \u{2192} T{awaited_tid}")
        } else {
            format!(" \u{2192} T{awaited_tid} ({awaited_label})")
        }
    } else if let Some(&promise_id) = state.promise_deps.get(&id) {
        let timer_task = state
            .timers
            .get(&promise_id)
            .and_then(|t| t.task_id);
        if let Some(tid) = timer_task {
            format!(" \u{2192} io:T{tid}")
        } else {
            format!(" \u{2192} p:{promise_id}")
        }
    } else {
        String::new()
    };

    let line = Line::from(vec![
        Span::styled(
            format!(" {indent}"),
            Style::default().fg(Color::DarkGray).bg(bg),
        ),
        Span::styled(
            exec_marker.to_string(),
            Style::default().fg(Color::Cyan).bg(bg),
        ),
        Span::styled(
            format!("{icon} "),
            Style::default().fg(color).bg(bg),
        ),
        Span::styled(
            format!("T{id}"),
            Style::default()
                .fg(if is_executing { Color::White } else { color })
                .bg(bg)
                .add_modifier(if is_executing {
                    Modifier::BOLD
                } else {
                    Modifier::empty()
                }),
        ),
        Span::styled(
            format!(" [{}]", task.status.label()),
            Style::default().fg(color).bg(bg),
        ),
        Span::styled(
            label_str,
            Style::default()
                .fg(if is_executing {
                    Color::White
                } else {
                    Color::Gray
                })
                .bg(bg),
        ),
        Span::styled(
            cancelled.to_string(),
            Style::default().fg(Color::Red).bg(bg),
        ),
        Span::styled(
            dep_annotation,
            Style::default().fg(Color::DarkGray).bg(bg),
        ),
    ]);
    lines.push(line);

    for (ci, &child) in task.children.iter().enumerate() {
        let child_is_last = ci == task.children.len() - 1;
        collect_task_lines(state, child, depth + 1, child_is_last, lines);
    }
}

fn render_task_queue(frame: &mut Frame, app: &App, area: Rect) {
    let block = Block::bordered()
        .title(" Task Queue ")
        .border_style(Style::default().fg(Color::DarkGray));

    let state = app.current_state();
    let mut lines: Vec<Line> = Vec::new();

    if state.work_queue.is_empty() {
        lines.push(Line::from(Span::styled(
            "  (empty)",
            Style::default().fg(Color::DarkGray),
        )));
    } else {
        for &id in &state.work_queue {
            let label = state
                .tasks
                .get(&id)
                .and_then(|t| t.label.as_deref())
                .unwrap_or("");
            lines.push(Line::from(vec![
                Span::styled(
                    format!("  task:{id}"),
                    Style::default().fg(Color::Yellow),
                ),
                Span::styled(
                    if label.is_empty() {
                        String::new()
                    } else {
                        format!(" {label}")
                    },
                    Style::default().fg(Color::White),
                ),
            ]));
        }
    }

    let p = Paragraph::new(lines).block(block);
    frame.render_widget(p, area);
}

fn render_io(frame: &mut Frame, app: &App, area: Rect) {
    let block = Block::bordered()
        .title(" I/O ")
        .border_style(Style::default().fg(Color::DarkGray));

    let state = app.current_state();
    let mut lines: Vec<Line> = Vec::new();

    if state.timers.is_empty() {
        lines.push(Line::from(Span::styled(
            "  (empty)",
            Style::default().fg(Color::DarkGray),
        )));
    } else {
        for timer in state.timers.values() {
            let task_label = timer
                .task_id
                .and_then(|id| state.tasks.get(&id))
                .and_then(|t| t.label.as_deref())
                .unwrap_or("");
            let task_str = timer
                .task_id
                .map(|id| format!(" task:{id}"))
                .unwrap_or_default();
            lines.push(Line::from(vec![
                Span::styled(
                    format!("  \u{23f1} promise:{}", timer.promise_id),
                    Style::default().fg(Color::Cyan),
                ),
                Span::styled(task_str, Style::default().fg(Color::DarkGray)),
                Span::styled(
                    if task_label.is_empty() {
                        String::new()
                    } else {
                        format!(" {task_label}")
                    },
                    Style::default().fg(Color::White),
                ),
            ]));
        }
    }

    let p = Paragraph::new(lines).block(block);
    frame.render_widget(p, area);
}

fn render_output(frame: &mut Frame, app: &App, area: Rect) {
    let block = Block::bordered()
        .title(" Output ")
        .border_style(Style::default().fg(Color::DarkGray));

    let state = app.current_state();
    let text = if state.stdout.is_empty() {
        "(empty)".into()
    } else {
        format!("{:?}", state.stdout)
    };

    let p = Paragraph::new(format!("  {text}"))
        .block(block)
        .style(Style::default().fg(Color::White));
    frame.render_widget(p, area);
}

fn render_source(frame: &mut Frame, app: &mut App, area: Rect) {
    let block = Block::bordered()
        .title(" Source ")
        .border_style(border_style(app, Panel::Source));

    let Some(source) = app.source_code.as_deref() else {
        let p = Paragraph::new("  (no source — use --source)")
            .block(block)
            .style(Style::default().fg(Color::DarkGray));
        frame.render_widget(p, area);
        return;
    };

    let state = app.current_state();
    let highlight = state.src_highlight.filter(|&(off, span)| off + span <= source.len());
    let task_region = state.active_task_region.filter(|&(off, span)| off + span <= source.len());

    if let Some((hl_off, _)) = highlight {
        let hl_line = source[..hl_off].matches('\n').count();
        let inner_height = area.height.saturating_sub(2) as usize;
        if inner_height > 0 {
            if hl_line < app.source_scroll {
                app.source_scroll = hl_line.saturating_sub(1);
            } else if hl_line >= app.source_scroll + inner_height {
                app.source_scroll = hl_line.saturating_sub(inner_height / 2);
            }
        }
    }

    let normal = Style::default().fg(Color::White);
    let dim = Style::default().fg(Color::DarkGray);
    let hl_style = Style::default()
        .fg(Color::White)
        .bg(Color::Rgb(60, 60, 80))
        .add_modifier(Modifier::BOLD);
    let text_style = if highlight.is_some() { dim } else { normal };
    let margin_dim = Span::styled(" ", dim);
    let margin_bar = Span::styled("\u{2502}", Style::default().fg(Color::Blue));

    let mut lines: Vec<Line> = Vec::new();
    let mut byte_pos: usize = 0;

    for line_text in source.split('\n') {
        let line_start = byte_pos;
        let line_end = byte_pos + line_text.len();

        let in_task = task_region.map_or(false, |(off, span)| {
            line_end > off && line_start < off + span
        });
        let margin = if in_task { margin_bar.clone() } else { margin_dim.clone() };

        if let Some((hl_off, hl_span)) = highlight {
            let hl_end = hl_off + hl_span;
            if line_end > hl_off && line_start < hl_end {
                let rel_start = hl_off.saturating_sub(line_start).min(line_text.len());
                let rel_end = (hl_end - line_start).min(line_text.len());

                let mut spans = vec![margin];
                if rel_start > 0 {
                    spans.push(Span::styled(&line_text[..rel_start], text_style));
                }
                spans.push(Span::styled(&line_text[rel_start..rel_end], hl_style));
                if rel_end < line_text.len() {
                    spans.push(Span::styled(&line_text[rel_end..], text_style));
                }
                lines.push(Line::from(spans));
            } else {
                lines.push(Line::from(vec![margin, Span::styled(line_text, text_style)]));
            }
        } else {
            lines.push(Line::from(vec![margin, Span::styled(line_text, text_style)]));
        }

        byte_pos = line_end + 1;
    }

    let p = Paragraph::new(lines)
        .block(block)
        .scroll((app.source_scroll as u16, 0));
    frame.render_widget(p, area);
}

fn render_detail(frame: &mut Frame, app: &App, area: Rect) {
    let block = Block::bordered()
        .title(" Detail ")
        .border_style(border_style(app, Panel::Detail));

    let mut text = match app.current_event() {
        Some(event) => format_event_detail(event),
        None => String::new(),
    };

    if let Some(event) = app.current_event() {
        if let Some(task_id) = event.get_u64("task-id") {
            let state = app.current_state();
            if let Some(task) = state.tasks.get(&task_id) {
                if task.label.is_some() || task.source.is_some() || !task.args.is_empty() {
                    text.push_str("\n\n  \u{2500}\u{2500} Task Info \u{2500}\u{2500}\n");
                    if let Some(label) = &task.label {
                        text.push_str(&format!("  label             {label}\n"));
                    }
                    if !task.args.is_empty() {
                        text.push_str("  args:\n");
                        for (k, v) in &task.args {
                            text.push_str(&format!("    {k:<16}{v}\n"));
                        }
                    }
                    if let Some(source) = &task.source {
                        text.push_str(&format!("  source            {source}\n"));
                    }
                }
            }
        }
    }

    let p = Paragraph::new(text)
        .block(block)
        .wrap(Wrap { trim: false })
        .scroll((app.detail_scroll as u16, 0));
    frame.render_widget(p, area);
}

fn format_event_detail(event: &crate::trace::TraceEvent) -> String {
    let mut keys: Vec<&String> = event.fields.keys().collect();
    keys.sort();
    let mut lines = Vec::new();
    for key in keys {
        let value = &event.fields[key];
        let value_str = match value {
            Value::String(s) => s.clone(),
            Value::Number(n) => n.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Null => "null".into(),
            other => serde_json::to_string(other).unwrap_or_default(),
        };
        lines.push(format!("  {key:<18} {value_str}"));
    }
    lines.join("\n")
}

fn render_status_bar(frame: &mut Frame, app: &App, area: Rect) {
    let pos = format!(
        " Event {}/{} ",
        app.cursor + 1,
        app.events.len()
    );
    let keys = "\u{2190}\u{2192}/hl step  g/G start/end  Tab focus  q quit ";
    let config_str = app
        .current_state()
        .config
        .iter()
        .map(|(k, v)| format!("{k}={v}"))
        .collect::<Vec<_>>()
        .join(" ");

    let line = Line::from(vec![
        Span::styled(pos, Style::default().fg(Color::Black).bg(Color::Cyan)),
        Span::styled(
            format!(" {config_str} "),
            Style::default().fg(Color::DarkGray),
        ),
        Span::styled(
            format!("{keys:>width$}", width = area.width as usize),
            Style::default().fg(Color::DarkGray),
        ),
    ]);

    let p = Paragraph::new(line);
    frame.render_widget(p, area);
}
