
-- Module for YANG Unsigned Integer 8bit
mod! YINT8{
    protecting (INT) .
    [Yint8]
    -- Err sentinel: if [l, u] bounds are out of range
    op errYint8 : -> Yint8 .
    -- Constructor creates Yint8 in bounds
    op mkYint8 : Int -> Yint8 [ctor] .
    -- Observer, works only if value is not errYint8
    op toInt : Yint8 -> Int .
    -- Range predicate check
    op inUint8 : Int -> Bool .

    var i : Int .
    -- Function Models
    ceq mkYint8(i) = errYint8 if not ((0 <= i) and (i <= 255)) .
    ceq toInt(mkYint8(i)) = i if (0 <= i) and (i <= 255) .
    eq inUint8(i) = (0 <= i) and (i <= 255) .

}

-- Module for ASN bounded Integer
mod! ASNBINT {
  protecting(INT) .
  [AsnInt]
  -- Constructor and observer 
  op mkAsnInt   : Int    -> AsnInt [ctor] .
  op fromAsnInt : AsnInt -> Int .

  -- Function Models
  var i : Int .
  eq fromAsnInt(mkAsnInt(i)) = i .
}

-- Module for Translation 
mod! INTTRANS {
  protecting(YINT8) .
  protecting(ASNBINT) .

  -- Forward and backward encoding for round-trip morphism 
  op asn2yang : AsnInt -> Yint8 .
  op yang2asn : Yint8  -> AsnInt .

  var i : Int .
  var y : Yint8 .

  eq asn2yang(mkAsnInt(i)) = mkYint8(i) .
  eq yang2asn(y)           = mkAsnInt(toInt(y)) .
}

-- Proof 0
-- Range containment
open INTTRANS .
  op x : -> Int .
  eq (0 <= x)   = true .
  eq (x <= 255) = true .
  --> If (0 <= x <= 255) is in range, it SHOULD reduce to true
  red inUint8(x) .
close .

-- Proof 1
-- Without constraint the translation fails
open INTTRANS .
  op x : -> Int .
  --> No predicates: SHOULD NOT reduce to true
  red fromAsnInt(yang2asn(asn2yang(mkAsnInt(x)))) = x .
close .

-- Proof 2
-- Round trip is satisfied
open INTTRANS .
  op x : -> Int .
  eq (0 <= x)   = true .
  eq (x <= 255) = true .
  --> Round-trip is satisfied SHOULD reduce to true
  red fromAsnInt(yang2asn(asn2yang(mkAsnInt(x)))) = x .
close .


