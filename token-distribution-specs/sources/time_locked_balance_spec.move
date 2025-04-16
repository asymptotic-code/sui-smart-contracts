module token_distribution_specs::time_locked_balance_spec;

use std::u64;
use sui::clock::{Clock};
use sui::balance::{Balance};
use token_distribution::time_locked_balance::{Self, TimeLockedBalance};
use token_distribution::primitives_util::timestamp_sec;

#[spec_only]
use prover::prover::{asserts, requires, ensures, old};
#[spec_only]
use std::integer::Integer;

#[spec_only]
use token_distribution_specs::utils::{start_timestamp_limit, require_start_timestamp_valid};

#[spec_only]
macro fun unlockable_amount_expected<$T>($self: &TimeLockedBalance<$T>, $now: u64): Integer {
    let self = $self;
    if (self.unlock_per_second() == 0
            || $now <= self.unlock_start_ts_sec()) {
        return std::integer::zero!()
    };

    let to_remain_locked = std::integer::mul(
        self.unlock_per_second().to_int(),
        std::integer::sub(
            self.final_unlock_ts_sec().to_int(),
            (u64::min(self.final_unlock_ts_sec(), $now)).to_int(),
        ),
    );

    let locked_amount_round =
        self.locked_balance() / self.unlock_per_second() * self.unlock_per_second();

    std::integer::sub(locked_amount_round.to_int(), to_remain_locked)
}

#[spec_only]
use fun TimeLockedBalance_inv as TimeLockedBalance.inv;
#[spec_only]
public fun TimeLockedBalance_inv<T>(self: &TimeLockedBalance<T>): bool {
    let mut timestamp = u64::max(self.unlock_start_ts_sec(), self.previous_unlock_at());
    if (timestamp > self.final_unlock_ts_sec()) {
        timestamp = self.final_unlock_ts_sec();
    };
    let final_unlock_ts_expected = if (self.unlock_per_second() > 0) {
        std::integer::add(
            timestamp.to_int(),
            (self.locked_balance() / self.unlock_per_second()).to_int(),
        )
    } else {
        std::integer::zero!()
    };
    let unlocked_balance_limit = std::integer::add(
        std::integer::mul(
            std::integer::sub(timestamp.to_int(), self.unlock_start_ts_sec().to_int()),
            self.unlock_per_second().to_int(),
        ),
        self.unlocked_balance().to_int(),
    );
    let locked_balance_extraneous = if (self.unlock_per_second() > 0) {
        std::integer::mod(
            self.locked_balance().to_int(),
            self.unlock_per_second().to_int(),
        )
    } else {
        std::integer::zero!()
    };
    let locked_balance_expected = if (self.final_unlock_ts_sec() > 0) {
        std::integer::add(
            locked_balance_extraneous,
            std::integer::mul(
                self.unlock_per_second().to_int(),
                std::integer::sub(self.final_unlock_ts_sec().to_int(), timestamp.to_int()),
            ),
        )
    } else {
        std::integer::zero!()
    };

    // check timestamp in correct order
    self.unlock_start_ts_sec() <= start_timestamp_limit!()
        && std::integer::lte(final_unlock_ts_expected, u64::max_value!().to_int())
        && (self.final_unlock_ts_sec()).to_int() == final_unlock_ts_expected
        && (self.final_unlock_ts_sec() == 0 || self.unlock_start_ts_sec() <= self.final_unlock_ts_sec())
        // && self.previous_unlock_at() <= self.final_unlock_ts_sec()
        // && (self.previous_unlock_at() == 0 || self.unlock_start_ts_sec() <= self.previous_unlock_at())
        // check balances
        && (self.final_unlock_ts_sec() == 0
            || self.locked_balance().to_int() == locked_balance_expected)
        && (self.final_unlock_ts_sec() == 0
            || self.final_unlock_ts_sec() == self.previous_unlock_at()
            || std::integer::lte(
                self.unlocked_balance().to_int(),
                unlocked_balance_limit
            ) //<= due to possible withdrawal
        )
        && std::integer::lte(
            std::integer::add(
                self.locked_balance().to_int(),
                self.unlocked_balance().to_int()
            ),
            u64::max_value!().to_int()
        )
}

#[spec(prove, target = time_locked_balance::create)]
public fun create_spec<T>(
    locked_balance: Balance<T>,
    unlock_start_ts_sec: u64,
    unlock_per_second: u64,
): TimeLockedBalance<T> {
    require_start_timestamp_valid!(unlock_start_ts_sec);
    let locked_balance_value = locked_balance.value();

    // asserts calc_final_unlock_ts_sec won't overflow
    //  =>  (start_ts + amount_to_issue / unlock_per_second) <= u64::max_value!()
    //  =>  amount_to_issue <= (u64::max_value!() - start_ts) * unlock_per_second
    let locked_balance_limit = std::integer::mul(
        (u64::max_value!() - unlock_start_ts_sec).to_int(),
        unlock_per_second.to_int(),
    );
    asserts(
        unlock_per_second == 0 || std::integer::lte(locked_balance_value.to_int(), locked_balance_limit),
    );

    let result = time_locked_balance::create(locked_balance, unlock_start_ts_sec, unlock_per_second);

    ensures(result.locked_balance() == locked_balance_value);
    ensures(result.unlock_start_ts_sec() == unlock_start_ts_sec);
    ensures(result.unlock_per_second() == unlock_per_second);
    ensures(result.unlocked_balance() == 0);
    ensures(result.previous_unlock_at() == 0);

    result
}

#[spec(prove, target = time_locked_balance::extraneous_locked_amount)]
public fun extraneous_locked_amount_spec<T>(self: &TimeLockedBalance<T>): u64 {
    let expected_result = if (self.unlock_per_second() == 0) {
        self.locked_balance()
    } else {
        self.locked_balance() % self.unlock_per_second()
    };

    let result = time_locked_balance::extraneous_locked_amount(self);

    ensures(result == expected_result);

    result
}

#[spec(prove, target = time_locked_balance::max_withdrawable)]
public fun max_withdrawable_spec<T>(self: &TimeLockedBalance<T>, clock: &Clock): u64 {
    requires(self.previous_unlock_at() <= timestamp_sec(clock));

    let expected_result = std::integer::add(
        unlockable_amount_expected!(self, timestamp_sec(clock)),
        self.unlocked_balance().to_int(),
    );

    let result = time_locked_balance::max_withdrawable(self, clock);

    ensures(result.to_int() == expected_result);

    result
}

#[spec(prove, target = time_locked_balance::remaining_unlock)]
public fun remaining_unlock_spec<T>(self: &TimeLockedBalance<T>, clock: &Clock): u64 {
    requires(self.previous_unlock_at() <= timestamp_sec(clock));

    let start = u64::max(self.unlock_start_ts_sec(), timestamp_sec(clock));
    let expected_result = if (start < self.final_unlock_ts_sec()) {
        (self.final_unlock_ts_sec() - start) * self.unlock_per_second()
    } else {
        0
    };

    let result = time_locked_balance::remaining_unlock(self, clock);

    ensures(result == expected_result);

    result
}

#[spec(prove, target = time_locked_balance::withdraw)]
public fun withdraw_spec<T>(
    self: &mut TimeLockedBalance<T>,
    amount: u64,
    clock: &Clock,
): Balance<T> {
    requires(self.previous_unlock_at() <= timestamp_sec(clock));

    let total_unlockable = std::integer::add(
        unlockable_amount_expected!(self, timestamp_sec(clock)),
        self.unlocked_balance().to_int(),
    );
    asserts(std::integer::lte(amount.to_int(), total_unlockable));

    let result = time_locked_balance::withdraw(self, amount, clock);

    ensures(result.value() == amount);
    ensures(
        total_unlockable == std::integer::add(
            amount.to_int(),
            self.unlocked_balance().to_int()
        ),
    );
    ensures(self.previous_unlock_at() == timestamp_sec(clock));

    result
}

#[spec(prove, target = time_locked_balance::withdraw_all)]
public fun withdraw_all_spec<T>(self: &mut TimeLockedBalance<T>, clock: &Clock): Balance<T> {
    requires(self.previous_unlock_at() <= timestamp_sec(clock));

    let expected_result = std::integer::add(
        unlockable_amount_expected!(self, timestamp_sec(clock)),
        self.unlocked_balance().to_int(),
    );

    let result = time_locked_balance::withdraw_all(self, clock);

    ensures(result.value().to_int() == expected_result);
    ensures(self.unlocked_balance() == 0);
    ensures(self.previous_unlock_at() == timestamp_sec(clock));

    result
}

#[spec(prove, target = time_locked_balance::top_up)]
public fun top_up_spec<T>(self: &mut TimeLockedBalance<T>, balance: Balance<T>, clock: &Clock) {
    requires(self.previous_unlock_at() <= timestamp_sec(clock));

    let total_coin_balance = std::integer::add(
        balance.value().to_int(),
        std::integer::add(
            self.unlocked_balance().to_int(),
            self.locked_balance().to_int(),
        ),
    );
    requires(std::integer::lte(total_coin_balance, u64::max_value!().to_int()));

    let unlocked_expected = unlockable_amount_expected!(self, timestamp_sec(clock));
    let unlocked_balance_expected = std::integer::add(
        self.unlocked_balance().to_int(),
        unlocked_expected,
    );
    let locked_balance_expected = std::integer::sub(
        std::integer::add(
            self.locked_balance().to_int(),
            balance.value().to_int(),
        ),
        unlocked_expected,
    );
    let final_unlock_ts_sec_old = self.final_unlock_ts_sec();

    // asserts calc_final_unlock_ts_sec won't overflow
    let start_ts = u64::max(self.unlock_start_ts_sec(), timestamp_sec(clock));
    let locked_balance_limit = std::integer::mul(
        (u64::max_value!() - start_ts).to_int(),
        self.unlock_per_second().to_int(),
    );
    asserts(
        self.unlock_per_second() == 0 || std::integer::lte(locked_balance_expected, locked_balance_limit),
    );

    time_locked_balance::top_up(self, balance, clock);

    ensures(self.unlocked_balance().to_int() == unlocked_balance_expected);
    ensures(self.locked_balance().to_int() == locked_balance_expected);
    ensures(self.previous_unlock_at() == timestamp_sec(clock));
    ensures(self.final_unlock_ts_sec() >= final_unlock_ts_sec_old);
}

#[spec(prove, target = time_locked_balance::change_unlock_per_second)]
public fun change_unlock_per_second_spec<T>(
    self: &mut TimeLockedBalance<T>,
    new_unlock_per_second: u64,
    clock: &Clock,
) {
    requires(self.previous_unlock_at() <= timestamp_sec(clock));

    let unlocked_expected = unlockable_amount_expected!(self, timestamp_sec(clock));
    let unlocked_balance_expected = std::integer::add(
        self.unlocked_balance().to_int(),
        unlocked_expected,
    );
    let locked_balance_expected = std::integer::sub(
        self.locked_balance().to_int(),
        unlocked_expected,
    );
    let final_unlock_ts_sec_old = self.final_unlock_ts_sec();
    let unlock_per_second_old = self.unlock_per_second();

    // asserts calc_final_unlock_ts_sec won't overflow
    let start_ts = u64::max(self.unlock_start_ts_sec(), timestamp_sec(clock));
    let locked_balance_limit = std::integer::mul(
        (u64::max_value!() - start_ts).to_int(),
        new_unlock_per_second.to_int(),
    );
    asserts(
        new_unlock_per_second == 0 || std::integer::lte(locked_balance_expected, locked_balance_limit),
    );

    time_locked_balance::change_unlock_per_second(self, new_unlock_per_second, clock);

    ensures(self.unlock_per_second() == new_unlock_per_second);
    ensures(self.previous_unlock_at() == timestamp_sec(clock));
    if (new_unlock_per_second > 0) {
        ensures(self.unlocked_balance().to_int() == unlocked_balance_expected);
        ensures(self.locked_balance().to_int() == locked_balance_expected);
    };
    // *note*: next one is heavy for a prover, but still provable
    if (
        new_unlock_per_second != 0
            && unlock_per_second_old != 0
            && self.previous_unlock_at() != self.final_unlock_ts_sec()
            && self.unlock_start_ts_sec() != self.final_unlock_ts_sec()
            && self.final_unlock_ts_sec() != final_unlock_ts_sec_old
    ) {
        ensures(
            (new_unlock_per_second > unlock_per_second_old)
                    == (self.final_unlock_ts_sec() < final_unlock_ts_sec_old),
        );
    };
}

#[spec(prove, target = time_locked_balance::change_unlock_start_ts_sec)]
public fun change_unlock_start_ts_sec_spec<T>(
    self: &mut TimeLockedBalance<T>,
    new_unlock_start_ts_sec: u64,
    clock: &Clock,
) {
    require_start_timestamp_valid!(new_unlock_start_ts_sec);
    let timestamp = timestamp_sec(clock);
    requires(self.previous_unlock_at() <= timestamp);
    require_start_timestamp_valid!(timestamp);

    let unlocked_expected = unlockable_amount_expected!(self, timestamp_sec(clock));
    let unlocked_balance_expected = std::integer::add(
        self.unlocked_balance().to_int(),
        unlocked_expected,
    );
    let locked_balance_expected = std::integer::sub(
        self.locked_balance().to_int(),
        unlocked_expected,
    );

    // asserts calc_final_unlock_ts_sec won't overflow
    //  =>  (start_ts + amount_to_issue / unlock_per_second) <= u64::max_value!()
    //  =>  amount_to_issue <= (u64::max_value!() - start_ts) * unlock_per_second
    let unlock_start_ts_actual = u64::max(new_unlock_start_ts_sec, timestamp);
    let locked_balance_limit = std::integer::mul(
        (u64::max_value!() - unlock_start_ts_actual).to_int(),
        self.unlock_per_second().to_int(),
    );
    asserts(
        self.unlock_per_second() == 0
            || std::integer::lte(locked_balance_expected, locked_balance_limit),
    );

    time_locked_balance::change_unlock_start_ts_sec(self, new_unlock_start_ts_sec, clock);

    ensures(self.unlock_start_ts_sec() == unlock_start_ts_actual);
    ensures(self.previous_unlock_at() == timestamp);

    ensures(self.unlocked_balance().to_int() == unlocked_balance_expected);
    ensures(self.locked_balance().to_int() == locked_balance_expected);
}
