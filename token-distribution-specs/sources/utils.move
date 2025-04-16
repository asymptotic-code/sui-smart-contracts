module token_distribution_specs::utils;

#[spec_only]
use prover::prover::{requires};

#[spec_only]
public macro fun start_timestamp_limit(): u64 {
    // to require timestamp near current time to simplify checking
    // this will help avoiding overflow while calculating final_unlock_ts_sec
    4102320000 //January 1, 2200
}

#[spec_only]
public macro fun require_start_timestamp_valid($unlock_start_ts_sec: u64) {
    requires($unlock_start_ts_sec <= start_timestamp_limit!()); //January 1, 2200
}
