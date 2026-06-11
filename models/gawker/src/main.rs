mod app;
mod state;
mod trace;
mod ui;

use clap::{Arg, Command};
use ratatui::crossterm::event::{
    self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode, KeyModifiers, MouseEventKind,
};
use ratatui::crossterm::execute;

fn main() {
    let matches = Command::new("gawker")
        .about("TUI debugger for async/await trace files")
        .arg(
            Arg::new("file")
                .help("Path to JSON-lines trace file")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::new("source")
                .long("source")
                .short('s')
                .help("Path to original source file for highlighting"),
        )
        .get_matches();

    let file: &String = matches.get_one("file").expect("file argument required");
    let events = trace::load_trace(file);
    let source_code = matches
        .get_one::<String>("source")
        .map(|p| std::fs::read_to_string(p).expect("failed to read source file"));
    if events.is_empty() {
        eprintln!("no events found in {file}");
        std::process::exit(1);
    }

    let mut app = app::App::new(events, source_code);
    let mut terminal = ratatui::init();
    execute!(std::io::stdout(), EnableMouseCapture).ok();

    while app.running {
        terminal
            .draw(|frame| ui::render(frame, &mut app))
            .expect("draw failed");

        match event::read() {
            Ok(Event::Key(key)) => match (key.code, key.modifiers) {
                (KeyCode::Char('q'), _) | (KeyCode::Esc, _) => app.running = false,
                (KeyCode::Char('c'), m) if m.contains(KeyModifiers::CONTROL) => {
                    app.running = false
                }
                (KeyCode::Right | KeyCode::Char('l'), _) => app.step_forward(),
                (KeyCode::Left | KeyCode::Char('h'), _) => app.step_back(),
                (KeyCode::Char('g'), _) => app.jump_start(),
                (KeyCode::Char('G'), _) => app.jump_end(),
                (KeyCode::Tab, _) => app.cycle_focus(),
                (KeyCode::Char('j') | KeyCode::Down, _) => app.scroll_down(),
                (KeyCode::Char('k') | KeyCode::Up, _) => app.scroll_up(),
                _ => {}
            },
            Ok(Event::Mouse(mouse)) => match mouse.kind {
                MouseEventKind::ScrollDown => app.scroll_down_at(mouse.column, mouse.row),
                MouseEventKind::ScrollUp => app.scroll_up_at(mouse.column, mouse.row),
                _ => {}
            },
            _ => {}
        }
    }

    execute!(std::io::stdout(), DisableMouseCapture).ok();
    ratatui::restore();
}
