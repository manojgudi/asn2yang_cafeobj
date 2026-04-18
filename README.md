CafeOBJ Proof sketch
=====

This repo contains CafeOBJ Proofs for the paper "Preserving Semantics for translating models from ASN.1 to YANG using CafeOBJ". It is tested to run on CafeOBJ 1.6.2 in an Ubuntu environment.

It contains three district proofs for three distinct sorts, and each one can be run individually- 
1. Integer sorts: 
```
$ cafeobj integer_proofs.mod
```
2. Record sorts:
```
$ cafeobj sequence_proofs.mod
```

3. Choice sorts:
```
$ cafeobj choice_proofs.mod
```


### Other artifacts:
compASNStr.asn   : ASN Compatible string type with restricted character set 
compYANGStr.yang : YANG Compatible strings type with restricted character set 
