-- Generic TYPE-X module implements generic sorts AsnX and YangX
mod! TYPE-X {
    [AsnX, YangX]
    -- forward backward functions
    op asnX2yangX : AsnX  -> YangX .
    op yangX2asnX : YangX -> AsnX  .

    var a : AsnX .
    -- Round-trip morphism works
    eq yangX2asnX(asnX2yangX(a)) = a .
}

-- Generic ASN.1 type Y with always true predicate
mod! TYPE-Y {

  [AsnY, YangY]

  op asnY2yangY : AsnY  -> YangY .
  op yangY2asnY : YangY -> AsnY  .

  var b : AsnY .

  -- Round-trip morphism works
  eq yangY2asnY(asnY2yangY(b)) = b .
}


-- Module implementing AsnSeq1 and YangGrp1 record sorts
mod! RECORD-MOD1 {
  protecting(TYPE-X) .

  [AsnSeq1, YangGrp1]

  op mkAsnSeq1    : AsnX     -> AsnSeq1 [ctor] .
  op mkYangGrp1   : YangX    -> YangGrp1 [ctor] .
  op getAsnFld1   : AsnSeq1  -> AsnX .
  op getYangFld1  : YangGrp1 -> YangX .

  op fwdSeq1 : AsnSeq1  -> YangGrp1 .
  op bwdSeq1 : YangGrp1 -> AsnSeq1 .

  var a : AsnX .
  var x : YangX .

  eq getAsnFld1(mkAsnSeq1(a))   = a .
  eq getYangFld1(mkYangGrp1(x)) = x .
  eq fwdSeq1(mkAsnSeq1(a))      = mkYangGrp1(asnX2yangX(a)) .
  eq bwdSeq1(mkYangGrp1(x))     = mkAsnSeq1(yangX2asnX(x)) .
}

open RECORD-MOD1 .
  --> Should reduce to true
  red getAsnFld1(bwdSeq1(fwdSeq1(mkAsnSeq1(a)))) = a .
close .


-- Generic 
mod! RECORD-MOD2 {
  protecting(TYPE-X) .
  protecting(TYPE-Y) .

  [AsnSeq2, YangGrp2]

  op mkAsnSeq2   : AsnX AsnY  -> AsnSeq2 [ctor] .
  op mkYangGrp2   : YangX YangY -> YangGrp2 [ctor] .
  op getAsnFld2X : AsnSeq2    -> AsnX .
  op getAsnFld2Y : AsnSeq2    -> AsnY .
  op getYangFld2X : YangGrp2    -> YangX .
  op getYangFld2Y : YangGrp2    -> YangY .

  op fwdSeq2 : AsnSeq2  -> YangGrp2 .
  op bwdSeq2 : YangGrp2 -> AsnSeq2 .

  var a : AsnX .
  var b : AsnY .
  var x : YangX .
  var y : YangY .

  eq getAsnFld2X(mkAsnSeq2(a, b))   = a .
  eq getAsnFld2Y(mkAsnSeq2(a, b))   = b .
  eq getYangFld2X(mkYangGrp2(x, y)) = x .
  eq getYangFld2Y(mkYangGrp2(x, y)) = y .
  eq fwdSeq2(mkAsnSeq2(a, b))       = mkYangGrp2(asnX2yangX(a), asnY2yangY(b)) .
  eq bwdSeq2(mkYangGrp2(x, y))      = mkAsnSeq2(yangX2asnX(x), yangY2asnY(y)) .
}


open RECORD-MOD2 .
  --> Both must print true
  red getAsnFld2X(bwdSeq2(fwdSeq2(mkAsnSeq2(a, b)))) = a .
  red getAsnFld2Y(bwdSeq2(fwdSeq2(mkAsnSeq2(a, b)))) = b .
close .


