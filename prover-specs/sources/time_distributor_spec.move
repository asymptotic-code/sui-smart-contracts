module prover_specs::time_distributor_spec;

use sui::balance::{Balance};
use token_distribution::time_distributor::{Self, TimeDistributor};
use token_distribution::time_locked_balance::{Self, TimeLockedBalance};
use prover_specs::time_locked_balance_spec::TimeLockedBalance_inv;

#[spec_only]
use prover::prover::{asserts, requires, ensures, old};
#[spec_only]
use std::integer::Integer;

#[spec_only]
use prover_specs::utils::{start_timestamp_limit, require_start_timestamp_valid};

#[spec_only]
use fun TimeDistributor_inv as TimeDistributor.inv;
#[spec_only]
fun TimeDistributor_inv<T, K: copy>(self: &TimeDistributor<T, K>): bool {
    TimeLockedBalance_inv(self.tlb())
        && self.size() == 0
            || self.tlb().unlock_per_second() > 0
                && self.total_weight() > 0
}

#[spec(prove, target = time_distributor::create)]
public fun create_spec<T, K: copy>(
    balance: Balance<T>,
    unlock_start_ts: u64,
): TimeDistributor<T, K> {
    require_start_timestamp_valid!(unlock_start_ts);

    let result = time_distributor::create<T, K>(balance, unlock_start_ts);

    ensures(result.size() == 0);
    ensures(result.total_weight() == 0);
    ensures(result.unlocked_balance() == 0);
    ensures(result.update_ts_sec() == 0);
    ensures(result.tlb().unlock_start_ts_sec() == unlock_start_ts);
    ensures(result.tlb().unlock_per_second() == 0);
    ensures(result.tlb().final_unlock_ts_sec() == 0);

    result
}
