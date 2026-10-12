use std::{env, error::Error, path::Path};

use lof::{
    core::{kernel::Context, terms::Term},
    modules::LoadedModule,
};

fn run() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    if args.len() < 2
        || !matches!(args[0].as_str(), "check" | "eval")
        || (args[0] == "check" && args.len() != 2)
        || (args[0] == "eval" && args.len() != 3)
    {
        return Err("usage: lof check FILE.lof | lof eval FILE.lof 'EXPRESSION'".into());
    }
    let loaded = LoadedModule::load(Path::new(&args[1]))?;
    if args[0] == "check" {
        println!(
            "checked {} ({} exports)",
            args[1],
            loaded.module().exports().len()
        );
    } else {
        let term = loaded.module().parse(&args[2])?;
        let ty = loaded.environment().infer(&Context::new(), &term)?;
        let normal = loaded.environment().normalize(&term);
        println!("type: {}", loaded.module().display(&ty));
        let mut numeral = &normal;
        let mut value = 0usize;
        while let Term::Succ(previous) = numeral {
            value += 1;
            numeral = previous;
        }
        if *numeral == Term::Zero {
            println!("{value}");
        } else {
            println!("{}", loaded.module().display(&normal));
        }
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
