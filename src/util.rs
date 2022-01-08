use bigdecimal::{
    BigDecimal,
    FromPrimitive,
    One,
    ToPrimitive,
};


pub fn factorial(n: &BigDecimal) -> Option<BigDecimal> {
    let x = n.to_i32()?;
    let mut product = BigDecimal::one();
    for n in 1 ..= x {
        let n = BigDecimal::from_i32(n)?;
        product *= n;
    }
    Some(product)
}
