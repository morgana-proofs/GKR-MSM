use std::env;
use std::error::Error;
use GKR_MSM::cleanup::protocols::pippenger::benchutils::{build_pippenger_data, run_pippenger, verify_pippenger};
use fork::{daemon, Fork};
use std::process::Command;

fn main() -> Result<(), Box<dyn Error>> {

    let args: Vec<String> = env::args().collect();
    let d_logsize = args.get(1).map(|s| s.parse().unwrap_or(8)).unwrap_or(8);
    let x_logsize = args.get(2).map(|s| s.parse().unwrap_or(10)).unwrap_or(10);
    let rng = &mut rand::thread_rng();
    let data = build_pippenger_data(rng, d_logsize, x_logsize);
    let config = data.config.clone();

    let output = run_pippenger(data);
    
    println!("{}", verify_pippenger(config, output));

    Ok(())
}