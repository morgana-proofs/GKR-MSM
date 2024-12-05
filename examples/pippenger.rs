use clap::{arg, command, value_parser};
use std::env;
use std::error::Error;
use std::fmt::Debug;
use clap::ArgAction::SetTrue;
use tracing::{instrument, Subscriber};
use tracing::dispatcher::DefaultGuard;
use tracing::level_filters::LevelFilter;
use GKR_MSM::cleanup::proof_transcript::{ProofTranscript2, TProofTranscript2};
use GKR_MSM::cleanup::protocols::pippenger::benchutils::{build_pippenger_data, run_pippenger, verify_pippenger};
use tracing_subscriber::{EnvFilter, fmt, prelude::*, reload, Registry, Layer};
use tracing_subscriber::fmt::format::FmtSpan;
use tracing_subscriber::layer::{Layered, SubscriberExt};
use tracing_subscriber::util::{SubscriberInitExt, TryInitError};
use tracing_tree::HierarchicalLayer;

fn main() -> Result<(), Box<dyn Error>> {
    let matches = command!() // requires `cargo` feature
        .arg(
            arg!(
                d_logsize: -d <NUMBER> "digit size"
            )
                .long("d-logsize")
                .required(false)
                .default_value("8")
                .value_parser(value_parser!(u8).range(2..10)),
        )
        .arg(
            arg!(
                x_logsize: -x <NUMBER> "input logsize"
            )
                .long("x-logsize")
                .visible_short_aliases(['N'])
                .visible_aliases(["N-logsize"])
                .required(false)
                .default_value("10")
                .value_parser(value_parser!(u8).range(8..20)),
        )
        .arg(
            arg!(
                nbits: -s <NUMBER> "scalar size"
            )
                .long("nbits")
                .visible_aliases(["scalar-logsize"])
                .required(false)
                .default_value("128")
                .value_parser(value_parser!(u16)),
        )
        .arg(
            arg!(
                commitment_log_multiplicity: <NUMBER> "log(number of d-logsize rows in one commitment)"
            )
                .long("commitment-log-multiplicity")
                .required(false)
                .default_value("0")
                .value_parser(value_parser!(u8)),
        )
        .arg(
            arg!(
                log: --log "should log events"
            )
                .action(SetTrue)
        )
        .get_matches();


    let d_logsize = *matches.get_one::<u8>("d_logsize").expect("digit size not set somehow") as usize;
    let x_logsize = *matches.get_one::<u8>("x_logsize").expect("input logsize  not set somehow") as usize;
    let num_bits = *matches.get_one::<u16>("nbits").expect("scalar size not set somehow") as usize;
    let commitment_log_multiplicity = *matches.get_one::<u8>("commitment_log_multiplicity").unwrap() as usize;
    let log = matches.get_flag("log");

    let tracer = tracing_subscriber::registry();
    let tracer = tracer
        .with(EnvFilter::builder()
            .with_default_directive(LevelFilter::INFO.into())
            .from_env_lossy());
    let tracer = tracer
        .with(tracing_span_tree::span_tree().aggregate(false));
    if log {
        tracer
            .with(tracing_subscriber::fmt::layer())
            .init();
    } else {
        tracer
            .init();
    }

    example(d_logsize, x_logsize, num_bits, commitment_log_multiplicity);

    Ok(())
}

#[instrument(skip_all)]
fn example(d_logsize: usize, x_logsize: usize, num_bits: usize, commitment_log_multiplicity: usize) {

    let rng = &mut rand::thread_rng();
    let data = build_pippenger_data(rng, d_logsize, x_logsize, num_bits, commitment_log_multiplicity);
    let config = data.config.clone();

    let mut transcript_p = ProofTranscript2::start_prover(b"fgstglsp");
    transcript_p.record_current_time("Start");
    let output = run_pippenger(&mut transcript_p, data);
    let time_records = transcript_p.time_records();
    let proof = transcript_p.end();

    println!("MSM params:");
    println!("log num points: {}, num bits: {}, d_logsize: {}", x_logsize, num_bits, d_logsize);
    // println!("Timings:");
    // for i in 0..time_records.len() - 1 {
    //     println!("{} : {}ms", time_records[i+1].1, (time_records[i+1].0 - time_records[i].0).as_millis());
    // }
    println!("Proof size: {} B", proof.len());
    let mut transcript_v = ProofTranscript2::start_verifier(b"fgstglsp", proof);
    verify_pippenger(&mut transcript_v, config, output);
    transcript_v.end();
    println!("Trace:");
}