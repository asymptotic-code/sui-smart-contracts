module amm_specs::pool_specs;

// ** WARNING **
// amm code contains registry and slippage checks which are not relevant for the specs
// specs needed to be updated

use amm::pool;
use amm::pool::{Pool, LP};

// use std::type_name::{Self, TypeName};
use std::u128;
use std::u64;
use sui::balance::{Balance, Supply};
// use sui::event;
// use sui::table::{Self, Table};

#[spec_only]
use prover::prover::{requires, ensures, asserts, old};

#[spec_only]
fun sqrt(x: u128): u64 {
    u128::sqrt(x) as u64
}

/// Invariant for the pool state.
#[spec_only]
use fun Pool_inv as Pool.inv;
#[spec_only]
fun Pool_inv<A, B>(self: &Pool<A, B>): bool {
    let l = self.lp_supply();
    let a = self.balance_a();
    let b = self.balance_b();

    // balances are 0 when LP supply is 0 or when LP supply > 0, both balances A and B are > 0
    ((l == 0 && a == 0 && b == 0) || (l > 0 && a > 0 && b > 0)) &&
    // the LP supply is always <= the geometric mean of the pool balances (this will make sure there is no overflow)
    l.to_int().mul(l.to_int()).lte(a.to_int().mul(b.to_int())) &&
    self.lp_fee_bps() <= pool::GET_BPS_IN_100_PCT() && self.admin_fee_pct() <= 100
}

#[spec_only]
macro fun ensures_a_and_b_price_increases<$A, $B>($pool: &Pool<$A, $B>, $old_pool: &Pool<$A, $B>) {
    let pool = $pool;
    let old_pool = $old_pool;

    let old_L = old_pool.lp_supply().to_int();
    let new_L = pool.lp_supply().to_int();

    // (L + dL) * A <= (A + dA) * L <=> L' * A <= A' * L
    let old_A = old_pool.balance_a().to_int();
    let new_A = pool.balance_a().to_int();
    ensures(new_L.mul(old_A).lte(new_A.mul(old_L)));

    // (L + dL) * B <= (B + dB) * L <=> L' * B <= B' * L
    let old_B = old_pool.balance_b().to_int();
    let new_B = pool.balance_b().to_int();
    ensures(new_L.mul(old_B).lte(new_B.mul(old_L)));
}

#[spec_only]
macro fun ensures_product_price_increases<$A, $B>($pool: &Pool<$A, $B>, $old_pool: &Pool<$A, $B>) {
    let pool = $pool;
    let old_pool = $old_pool;

    let old_L = old_pool.lp_supply().to_int();
    let new_L = pool.lp_supply().to_int();
    let old_A = old_pool.balance_a().to_int();
    let new_A = pool.balance_a().to_int();
    let old_B = old_pool.balance_b().to_int();
    let new_B = pool.balance_b().to_int();

    // L'^2 * A * B <= L^2 * A' * B'
    ensures(new_L.mul(new_L).mul(old_A).mul(old_B).lte(old_L.mul(old_L).mul(new_A).mul(new_B)));
}

#[spec_only]
macro fun requires_balance_leq_supply<$T>($balance: &Balance<$T>, $supply: &Supply<$T>) {
    let balance = $balance;
    let supply = $supply;
    requires(balance.value() <= supply.supply_value());
}

#[spec_only]
macro fun requires_balance_sum_no_overflow<$T>($balance0: &Balance<$T>, $balance1: &Balance<$T>) {
    let balance0 = $balance0;
    let balance1 = $balance1;
    requires(balance0.value().to_int().add(balance1.value().to_int()).lt(u64::max_value!().to_int()));
}

/* ================= specs ================= */

// #[spec(prove, target = pool::create)]
// fun create_spec<A, B>(
//     init_a: Balance<A>,
//     init_b: Balance<B>,
//     lp_fee_bps: u64,
//     admin_fee_pct: u64,
//     ctx: &mut TxContext,
// ): Balance<LP<A, B>> {
//     asserts(init_a.value() > 0 && init_b.value() > 0);
//     asserts(lp_fee_bps < pool::GET_BPS_IN_100_PCT());
//     asserts(admin_fee_pct <= 100);

//     let result = pool::create(init_a, init_b, lp_fee_bps, admin_fee_pct, ctx);

//     ensures(result.value() > 0);

//     result
// }

// #[spec(prove)]
// fun deposit_spec<A, B>(
//     pool: &mut Pool<A, B>,
//     input_a: Balance<A>,
//     input_b: Balance<B>,
// ): (Balance<A>, Balance<B>, Balance<LP<A, B>>) {
//     requires_balance_sum_no_overflow!(&pool.balance_a, &input_a);
//     requires_balance_sum_no_overflow!(&pool.balance_b, &input_b);

//     // regarding asserts:
//     // there aren't any overflows or divisions by zero, because there aren't any asserts
//     // (the list of assert conditions is exhaustive)

//     let old_pool = old!(pool);

//     let (result_input_a, result_input_b, result_lp) = deposit(pool, input_a, input_b);

//     // prove that depositing liquidity always returns LPs of smaller value then what was deposited
//     ensures_a_and_b_price_increases!(pool, old_pool);

//     (result_input_a, result_input_b, result_lp)
// }

// #[spec(prove)]
// fun generic_deposit_spec(
//     input_a_value: u64,
//     input_b_value: u64,
//     pool_a_value: u64,
//     pool_b_value: u64,
//     pool_lp_value: u64,
// ): (u64, u64, u64) {
//     let old_A = pool_a_value.to_int();
//     let old_B = pool_b_value.to_int();
//     let old_L = pool_lp_value.to_int();

//     requires(0 < input_a_value);
//     requires(0 < input_b_value);
//     requires(old_A.add(input_a_value.to_int()).lte(u64::max_value!().to_int()));
//     requires(old_B.add(input_b_value.to_int()).lte(u64::max_value!().to_int()));

//     requires(old_L.is_zero!() && old_A.is_zero!() && old_B.is_zero!() || !old_L.is_zero!() && !old_A.is_zero!() && !old_B.is_zero!());

//     // L^2 <= A * B
//     requires(old_L.mul(old_L).lte(old_A.mul(old_B)));

//     // regarding asserts:
//     // there aren't any overflows or divisions by zero, because there aren't any asserts
//     // (the list of assert conditions is exhaustive)

//     let (deposit_a, deposit_b, lp_to_issue) = generic_deposit(
//         input_a_value,
//         input_b_value,
//         pool_a_value,
//         pool_b_value,
//         pool_lp_value
//     );

//     let new_A = old_A.add(deposit_a.to_int());
//     let new_B = old_B.add(deposit_b.to_int());
//     let new_L = old_L.add(lp_to_issue.to_int());

//     ensures(deposit_a <= input_a_value);
//     ensures(deposit_b <= input_b_value);
//     ensures(new_L.lte(u64::max_value!().to_int()));

//     ensures(new_L.is_zero!() && new_A.is_zero!() && new_B.is_zero!() || !new_L.is_zero!() && !new_A.is_zero!() && !new_B.is_zero!());

//     // (L + dL) * A <= (A + dA) * L <=> L' * A <= A' * L
//     ensures(new_L.mul(old_A).lte(new_A.mul(old_L)));
//     // (L + dL) * B <= (B + dB) * L <=> L' * B <= B' * L
//     ensures(new_L.mul(old_B).lte(new_B.mul(old_L)));
//     // L^2 <= A * B
//     ensures(new_L.mul(new_L).lte(new_A.mul(new_B)));

//     (deposit_a, deposit_b, lp_to_issue)
// }

// #[spec(prove)]
// fun withdraw_spec<A, B>(
//     pool: &mut Pool<A, B>,
//     lp_in: Balance<LP<A, B>>
// ): (Balance<A>, Balance<B>) {
//     requires_balance_leq_supply!(&lp_in, &pool.lp_supply);

//     // regarding asserts:
//     // there aren't any overflows or divisions by zero, because there aren't any asserts
//     // (the list of assert conditions is exhaustive)

//     let old_pool = old!(pool);

//     let (result_a, result_b) = withdraw(pool, lp_in);

//     // the invariant `Pool_inv` implies that when all LPs are withdrawn, both A and B go to zero

//     // prove that withdrawing liquidity always returns A and B of smaller value then what was withdrawn
//     ensures_a_and_b_price_increases!(pool, old_pool);

//     (result_a, result_b)
// }

// #[spec(prove)]
// fun swap_a_spec<A, B>(
//     pool: &mut Pool<A, B>,
//     input: Balance<A>,
// ): Balance<B> {
//     requires_balance_sum_no_overflow!(&pool.balance_a, &input);
//     requires_balance_leq_supply!(&pool.admin_fee_balance, &pool.lp_supply);

//     // swapping on an empty pool is not possible
//     if (input.value() > 0) {
//         asserts(pool.lp_supply() > 0);
//     };

//     // regarding asserts:
//     // there aren't any overflows or divisions by zero, because there aren't any other asserts
//     // (the list of asserts conditions is exhaustive)

//     let old_pool = old!(pool);

//     let result = swap_a(pool, input);

//     // L'^2 * A * B <= L^2 * A' * B'
//     ensures_product_price_increases!(pool, old_pool);

//     // swapping on a non-empty pool can never cause any pool balance to go to zero
//     if (old_pool.lp_supply() > 0) {
//         ensures(pool.balance_a() > 0);
//         ensures(pool.balance_b() > 0);
//     };

//     result
// }

// #[spec(prove)]
// fun swap_b_spec<A, B>(
//     pool: &mut Pool<A, B>,
//     input: Balance<B>,
// ): Balance<A> {
//     requires_balance_sum_no_overflow!(&pool.balance_b, &input);
//     requires_balance_leq_supply!(&pool.admin_fee_balance, &pool.lp_supply);

//     // swapping on an empty pool is not possible
//     if (input.value() > 0) {
//         asserts(pool.lp_supply() > 0);
//     };

//     // regarding asserts:
//     // there aren't any overflows or divisions by zero, because there aren't any other asserts
//     // (the list of asserts conditions is exhaustive)

//     let old_pool = old!(pool);

//     let result = swap_b(pool, input);

//     // L'^2 * A * B <= L^2 * A' * B'
//     ensures_product_price_increases!(pool, old_pool);

//     // swapping on a non-empty pool can never cause any pool balance to go to zero
//     if (old_pool.lp_supply() > 0) {
//         ensures(pool.balance_a() > 0);
//         ensures(pool.balance_b() > 0);
//     };

//     result
// }

// #[spec(prove)]
// fun calc_swap_result_spec(
//     i_value: u64,
//     i_pool_value: u64,
//     o_pool_value: u64,
//     pool_lp_value: u64,
//     lp_fee_bps: u64,
//     admin_fee_pct: u64,
// ): (u64, u64) {
//     requires(0 < i_pool_value);
//     requires(0 < o_pool_value);
//     requires(0 < pool_lp_value);

//     let old_A = i_pool_value.to_int();
//     let old_B = o_pool_value.to_int();
//     let old_L = pool_lp_value.to_int();
//     let new_A = old_A.add(i_value.to_int());

//     requires(new_A.lt(u64::max_value!().to_int()));

//     // L^2 <= A * B
//     requires(old_L.mul(old_L).lte(old_A.mul(old_B)));

//     requires(lp_fee_bps <= BPS_IN_100_PCT);
//     requires(admin_fee_pct <= 100);

//     // regarding asserts:
//     // there aren't any overflows or divisions by zero, because there aren't any asserts
//     // (the list of assert conditions is exhaustive)

//     let (out_value, admin_fee_in_lp) = calc_swap_result(
//         i_value,
//         i_pool_value,
//         o_pool_value,
//         pool_lp_value,
//         lp_fee_bps,
//         admin_fee_pct,
//     );

//     let new_B = old_B.sub(out_value.to_int());
//     let new_L = old_L.add(admin_fee_in_lp.to_int());

//     ensures(out_value <= o_pool_value);
//     ensures(new_L.lte(u64::max_value!().to_int()));

//     // L'^2 * A * B <= L^2 * A' * B'
//     ensures(new_L.mul(new_L).mul(old_A).mul(old_B).lte(old_L.mul(old_L).mul(new_A).mul(new_B)));
//     // help the prover with `swap_b`
//     // L'^2 * B * A <= L^2 * B' * A'
//     ensures(new_L.mul(new_L).mul(old_B).mul(old_A).lte(old_L.mul(old_L).mul(new_B).mul(new_A)));
//     // L'^2 <= A' * B'
//     ensures(new_L.mul(new_L).lte(new_A.mul(new_B)));

//     (out_value, admin_fee_in_lp)
// }

// #[spec(prove)]
// fun admin_set_fees_spec<A, B>(
//     pool: &mut Pool<A, B>,
//     cap: &AdminCap,
//     lp_fee_bps: u64,
//     admin_fee_pct: u64,
// ) {
//     asserts(lp_fee_bps < BPS_IN_100_PCT);
//     asserts(admin_fee_pct <= 100);
//     admin_set_fees(pool, cap, lp_fee_bps, admin_fee_pct);
// }

#[spec]
fun sqrt_spec(x: u128): u64 {
    let result = sqrt(x);
    ensures((result as u128) * (result as u128) <= x);
    ensures(((result as u256) + 1) * ((result as u256) + 1) > x as u256);
    result
}
