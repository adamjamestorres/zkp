pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    signal input in;
    signal output out;
    component n2b = Num2Bits(b+2);
    n2b.in <== in;
    out <== 1-n2b.bits[b];
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(shift) {
    signal input x;
    signal output y;

    signal rem <-- x % (1 << shift);
    component num2bits = Num2Bits(shift);
    num2bits.in <== rem;

    y <-- (x - rem) / (1 << shift);
    x === y * (1 << shift) + rem;
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    component right_shift = RightShift(round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;
    assert( skip_checks == 1 || shift < shift_bound);
    y <--(x << shift);
    assert(y >= 0);
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.

 */
template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];
    // Temporary one_hot vector
    var one_hot_temp[b];
    assert( skip_checks == 1 || in != 0);   
    component n2b = Num2Bits(b+1);
    n2b.in <== in;
    // 1. Copy over all of the bits 
    for (var i = 0; i < b; i++) {
        one_hot_temp[i] = n2b.bits[i];
    }
    // Converts lower bits from the b-2th bit
    for (var i = b-2; i >= 0; i--) {
        // If one_hot_temp[i] = 1 and one_hot_temp[i+1] = 1 then this will be 0
        // If one_hot_temp[i] = 0 and one_hot_temp[i+1] = 1 then this will be 1
        // If one_hot_temp[i] = 1 and one_hot_temp[i+1] = 0 then this will be 0
        // If one_hot_temp[i] = 0 and one_hot_temp[i+1] = 0 then this will be 0
        one_hot_temp[i] = one_hot_temp[i] + one_hot_temp[i + 1] * (1 - one_hot_temp[i]);
    }
     // start hot encoding from the b-2th bit
    one_hot[b-1] <== one_hot_temp[b-1];
    for (var i = b-2; i >= 0; i--) {
        one_hot[i] <--  one_hot_temp[i] * (1 - one_hot_temp[i + 1]);
    }
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.


def normalize(k, p, P, e, m):
    assert(P > p and m != 0)
    ''' Let ell be the MSNZB of m. Recall that m is a P+1-bit number with precision p.
        We want to make the mantissa normalized, i.e., bring it to the range [2^P, 2^(P+1)), by shifting it left by P-ell bits.
        Consequently, we need to decrement the exponent by P-ell.
        At the same time, we are also increasing precision of mantissa from p to P, so we also need to increment the exponent by P-p.
        Overall, this means adding (P-p)-(P-ell) = ell-p to the exponent.
    '''
    ell = msnzb(m, P+1)
    m <<= (P - ell)
    e = e + ell - p
    return (e, m)
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;

    assert(P > p);
    assert( skip_checks == 1 || m != 0);

    // helper signals and components 
    component ls = LeftShift(252);
    component msn = MSNZB(P+1);
    msn.in <== m;
    msn.skip_checks <== skip_checks;
    signal one_hot[P+1] <== msn.one_hot;
    //   ell = msnzb(m, P+1)
    //   e = e + ell - p
    var ell = 0;
    for (var i = 0; i <= P; i++) {
        ell += i * one_hot[i];
    }
    var m_shift = P-ell;
    e_out <== (e + ell - p);
    //   m <== (P - ell)
    ls.x <== m;
    ls.shift <== m_shift;
    ls.skip_checks <== skip_checks;
    m_out <== ls.y;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.

''' Adds two floating-point numbers.
    The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m`.
'''
def float_add(k, p, e_1, m_1, e_2, m_2):
    check_well_formedness(k, p, e_1, m_1)
    check_well_formedness(k, p, e_2, m_2)

    ''' Arrange numbers in the order of their magnitude.
        Although not the same as magnitude, comparing e_1 || m_1 against e_2 || m_2 suffices to compare magnitudes.
    '''
    mgn_1 = (e_1 << (p+1)) + m_1
    mgn_2 = (e_2 << (p+1)) + m_2
    ''' comparison over k+p+1 bits '''
    if mgn_1 > mgn_2:
        (alpha_e, alpha_m) = (e_1, m_1)
        (beta_e, beta_m) = (e_2, m_2)
    else:
        (alpha_e, alpha_m) = (e_2, m_2)
        (beta_e, beta_m) = (e_1, m_1)

    diff = alpha_e - beta_e
    if diff > p + 1 or alpha_e == 0:
        return (alpha_e, alpha_m)
    else:
        alpha_m <<= diff
        ''' m fits in 2*p+2 bits '''
        m = alpha_m + beta_m
        e = beta_e
        (normalized_e, normalized_m) = normalize(k, p, 2*p+1, e, m)
        (e_out, m_out) = round_nearest_and_check(k, p, 2*p+1, normalized_e, normalized_m)

        return (e_out, m_out)

 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    component c1 = CheckWellFormedness(k, p);
    component c2 = CheckWellFormedness(k, p);
    c1.e <== e[0];
    c1.m <== m[0];
    c2.e <== e[1];
    c2.m <== m[1];
    /*   
        mgn_1 = (e_1 << (p+1)) + m_1
        mgn_2 = (e_2 << (p+1)) + m_2
        ''' comparison over k+p+1 bits '''
        if mgn_1 > mgn_2:
            (alpha_e, alpha_m) = (e_1, m_1)
            (beta_e, beta_m) = (e_2, m_2)
        else:
            (alpha_e, alpha_m) = (e_2, m_2)
            (beta_e, beta_m) = (e_1, m_1)
    */
    signal x <-- (e[0] << (p + 1)) ;
    signal y <-- (e[1] << (p + 1)) ;

    signal mgn1 <== x + m[0];
    signal mgn2 <== y + m[1];
    /*

    if diff > p + 1 or alpha_e == 0:
        return (alpha_e, alpha_m)
    else:
        alpha_m <<= diff
        ''' m fits in 2*p+2 bits '''
        m = alpha_m + beta_m
        e = beta_e
        (normalized_e, normalized_m) = normalize(k, p, 2*p+1, e, m)
        (e_out, m_out) = round_nearest_and_check(k, p, 2*p+1, normalized_e, normalized_m)

        return (e_out, m_out)

    */
    signal swp <-- mgn1 > mgn2;
     // Alpha E and Beta E/M
    signal alpha_e <-- swp ? e[0] : e[1];
    signal beta_e <-- swp ? e[1] : e[0];
    signal alpha_m <-- swp ? m[0] : m[1];
    signal beta_m <-- swp? m[1] : m[0];
    // According to sample code: diff = alpha_e - beta_e
    signal diff <-- alpha_e - beta_e;
    signal gt <-- diff > (p + 1) ? 1 : 0;
    signal res_condition <-- alpha_e == 0 || gt;
    /*
    
    else:
        alpha_m <<= diff
        ''' m fits in 2*p+2 bits '''
        m = alpha_m + beta_m
        e = beta_e
        (normalized_e, normalized_m) = normalize(k, p, 2*p+1, e, m)
        (e_out, m_out) = round_nearest_and_check(k, p, 2*p+1, normalized_e, normalized_m)

        return (e_out, m_out)
    */
    signal alpha_temp_m <-- alpha_m << diff;
    signal m_temp <-- alpha_temp_m  + beta_m;

    component normalized = Normalize(k, p, 2*p + 1);
    normalized.m <== m_temp;
    normalized.e <== beta_e;
    
    normalized.skip_checks <== res_condition;

    component rounded_check = RoundAndCheck(k, p, 2*p + 1);
    /*
        e = beta_e
        (normalized_e, normalized_m) = normalize(k, p, 2*p+1, e, m)
        (e_out, m_out) = round_nearest_and_check(k, p, 2*p+1, normalized_e, normalized_m)
    */
    signal rounded_e <-- res_condition ? 1 : normalized.e_out ;
    signal rounded_m <-- res_condition ? 1 : normalized.m_out ;
    rounded_check.e <== rounded_e;
    rounded_check.m <== rounded_m;
    m_out <-- res_condition ? alpha_m : rounded_check.m_out;
    e_out <-- res_condition ? alpha_e : rounded_check.e_out;
}