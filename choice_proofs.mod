-- Generic TYPE-X module implements generic sorts AsnX and YangX
mod! TYPE-X {
    [AsnX, YangX]
    -- forward backward functions
    op asnX2yangX : AsnX  -> YangX .
    op yangX2asnX : YangX -> AsnX  .

    var a : AsnX .
    -- Round-trip condition works
    eq yangX2asnX(asnX2yangX(a)) = a .
}

-- Generic ASN.1 type Y with always true predicate | Same like TYPE-X
mod! TYPE-Y {
  [AsnY, YangY]
    -- forward backward functions
  op asnY2yangY : AsnY  -> YangY .
  op yangY2asnY : YangY -> AsnY  .

  var b : AsnY .
  -- Round-trip condition works
  eq yangY2asnY(asnY2yangY(b)) = b .
}


mod! CHOICE-T{
    protecting(TYPE-X)
    protecting(TYPE-Y)

    [AsnChoice, YangChoice]

    -- Constructors which Tag ASN.1 values
    op aTag1 : AsnX -> AsnChoice .
    -- Unique Tag but same type as aTag1
    op aTag3 : AsnX -> AsnChoice .
    op aTag2 : AsnY -> AsnChoice .

    -- Constructors which Tag YANG values
    op yTag1 : YangX -> YangChoice .
    op yTag2 : YangY -> YangChoice .

    -- Observers
    op gtaTag1 : AsnChoice  -> AsnX .
    op gtaTag3 : AsnChoice  -> AsnX . -- For same type but different tag

    op gtaTag2 : AsnChoice  -> AsnY .
    op gtaTag3 : AsnChoice  -> AsnY .
    op gtyTag1 : YangChoice -> YangX .
    op gtyTag2 : YangChoice -> YangY .

    -- Check distinct tags
    op isaTag1 : AsnChoice -> Bool .
    op isaTag2 : AsnChoice -> Bool .

    -- variables i.e. values of sorts
    var a : AsnX .
    var b : AsnY .
    var p : YangX .
    var q : YangY .

    -- Function models for observers
    eq gtaTag1(aTag1(a)) = a .
    eq gtaTag3(aTag3(a)) = a . -- For same type but different tag
    eq gtaTag2(aTag2(b)) = b .
    eq gtyTag1(yTag1(p)) = p .
    eq gtyTag2(yTag2(q)) = q .

    -- Function models for checking distinct type
    eq isaTag1(aTag1(a)) = true .
    eq isaTag1(aTag2(b)) = false .

    -- Function models for individual round trips
    op fwdChoice : AsnChoice -> YangChoice .
    eq fwdChoice(aTag1(a)) = yTag1(asnX2yangX(a)) .
    eq fwdChoice(aTag2(b)) = yTag2(asnY2yangY(b)) .

    op bwdChoice : YangChoice -> AsnChoice .
    eq bwdChoice(yTag1(p)) = aTag1(yangX2asnX(p)) .
    eq bwdChoice(yTag2(q)) = aTag2(yangY2asnY(q)) .
}

-- Proof: Tag1 and Tag2 round-trip
open CHOICE-T .
    --> Shows value of Tag1 obeys CHOICE round-trip condition
    red gtaTag1(bwdChoice(fwdChoice(aTag1(a)))) = a .
    --> Shows value of Tag2 obeys CHOICE round-trip condition
    red gtaTag2(bwdChoice(fwdChoice(aTag2(b)))) = b .
close .

-- Proof: Tag Distinctness
open CHOICE-T .
    op o : -> AsnX .
    op m : -> AsnY .
   --> Tag1 is Tag for AsnX type, so TRUE for (o:AsnX)
   red isaTag1(aTag1(o)) .
   --> Tag3 is also a Tag for AsnX, but CafeOBJ identifies it and doesnt reduce!
   red isaTag1(aTag3(o)) .
   --> Tag2 is Tag for AsnY type, so FALSE for (m:AsnY)
   red isaTag1(aTag2(m)) .
close
