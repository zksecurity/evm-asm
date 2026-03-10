#![no_std]
#![no_main]

use ethereum_types::U256;

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

// Each function uses #[no_mangle] #[inline(never)] extern "C" to force
// standalone emission in the assembly output.

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_add(a: &U256, b: &U256) -> U256 {
    a.overflowing_add(*b).0
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_sub(a: &U256, b: &U256) -> U256 {
    a.overflowing_sub(*b).0
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_mul(a: &U256, b: &U256) -> U256 {
    a.overflowing_mul(*b).0
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_div(a: &U256, b: &U256) -> U256 {
    a.checked_div(*b).unwrap_or(U256::zero())
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_mod(a: &U256, b: &U256) -> U256 {
    a.checked_rem(*b).unwrap_or(U256::zero())
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_and(a: &U256, b: &U256) -> U256 {
    *a & *b
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_or(a: &U256, b: &U256) -> U256 {
    *a | *b
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_xor(a: &U256, b: &U256) -> U256 {
    *a ^ *b
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_not(a: &U256) -> U256 {
    !*a
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_lt(a: &U256, b: &U256) -> u64 {
    if *a < *b { 1 } else { 0 }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_gt(a: &U256, b: &U256) -> u64 {
    if *a > *b { 1 } else { 0 }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_eq(a: &U256, b: &U256) -> u64 {
    if *a == *b { 1 } else { 0 }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_iszero(a: &U256) -> u64 {
    if a.is_zero() { 1 } else { 0 }
}

// Signed comparison: interpret as two's complement
#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_slt(a: &U256, b: &U256) -> u64 {
    let a_sign = a.bit(255);
    let b_sign = b.bit(255);
    let result = if a_sign != b_sign {
        // a is negative (sign=1), b is positive (sign=0) => a < b
        if a_sign { true } else { false }
    } else {
        *a < *b
    };
    if result { 1 } else { 0 }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_sgt(a: &U256, b: &U256) -> u64 {
    let a_sign = a.bit(255);
    let b_sign = b.bit(255);
    let result = if a_sign != b_sign {
        if b_sign { true } else { false }
    } else {
        *a > *b
    };
    if result { 1 } else { 0 }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_shr(shift: &U256, value: &U256) -> U256 {
    if *shift >= U256::from(256u32) {
        U256::zero()
    } else {
        *value >> shift.as_u32() as usize
    }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_shl(shift: &U256, value: &U256) -> U256 {
    if *shift >= U256::from(256u32) {
        U256::zero()
    } else {
        *value << shift.as_u32() as usize
    }
}

// SAR: arithmetic right shift (ethrex implementation)
#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_sar(shift: &U256, value: &U256) -> U256 {
    let sign = value.bit(255);
    if *shift >= U256::from(256u32) {
        if sign { U256::MAX } else { U256::zero() }
    } else {
        let shifted = *value >> shift.as_u32() as usize;
        if sign {
            // Fill upper bits with ones
            let shift_amount = shift.as_u32() as usize;
            let mask = U256::MAX << (256 - shift_amount);
            shifted | mask
        } else {
            shifted
        }
    }
}

// BYTE: extract byte at index from value (big-endian indexing)
#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_byte(index: &U256, value: &U256) -> U256 {
    if *index >= U256::from(32u32) {
        U256::zero()
    } else {
        U256::from(value.byte(31 - index.as_u32() as usize))
    }
}

// SIGNEXTEND: sign-extend from byte b of value x
#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_signextend(b: &U256, x: &U256) -> U256 {
    if *b < U256::from(31u32) {
        let bit_index = b.as_u32() as usize * 8 + 7;
        let mask = (U256::one() << bit_index) - U256::one();
        if x.bit(bit_index) {
            *x | !mask
        } else {
            *x & mask
        }
    } else {
        *x
    }
}

// SWAP: swap two U256 values via pointers
#[no_mangle]
#[inline(never)]
pub extern "C" fn u256_swap(a: &mut U256, b: &mut U256) {
    core::mem::swap(a, b);
}
