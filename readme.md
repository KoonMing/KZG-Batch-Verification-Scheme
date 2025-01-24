## Introduction
This is a fork from github.com/crate-crypto/go-eth-kzg and it provides two batch verification algorithms that are more efficient than that in the original repo, in decending order:
- [internal -> kzg -> kzg_verify.go -> NewBatchVerifyMultiPoints](https://github.com/sytansy/go-kzg-4844/blob/389d29f6c57d1c384ad9f7dd14489304111c1a56/internal/kzg/kzg_verify.go#L397)
- [internal -> kzg -> kzg_verify.go -> InvBatchVerifyMultiPoints](https://github.com/sytansy/go-kzg-4844/blob/389d29f6c57d1c384ad9f7dd14489304111c1a56/internal/kzg/kzg_verify.go#L530)

The benchmark is done on Intel Core i9-14900HX CPU (2.20 GHz), 32 GB of RAM, Windows 11 Home. The result is below (in ns) where Unsafe is the naive proof aggregation without the randomized linear combination challenges:
| Openings | Original | Inv | New | Unsafe |
| --- | --- | --- | --- | --- |
| 1    | 662,288 | 662,580 | 583,273 | 661,873 |
| 2    | 1,164,088 | 976,287 | 1,146,674 | 912,912 |
| 4    | 1,079,543 | 1,121,269 | 1,182,132 | 921,742 |
| 8    | 1,238,596 | 1,053,881 | 1,182,002 | 962,471 |
| 16   | 1,220,163 | 1,151,709 | 1,229,665 | 1,030,726 |
| 32   | 1,424,648 | 1,483,559 | 1,378,267 | 1,155,115 |
| 64   | 1,918,847 | 1,766,635 | 1,475,809 | 1,316,069 |
| 128  | 2,449,261 | 2,235,119 | 1,712,561 | 1,609,571 |
| 256  | 3,217,386 | 3,372,530 | 2,299,085 | 2,038,715 |
| 512  | 5,506,765 | 5,254,228 | 4,074,118 | 3,038,276 |
| 1024 | 13,220,107 | 12,092,042 | 8,116,553 | 6,301,602 |

It also provides two alternatives for KZG proof verification that are more efficiet than that in the original repo:
- [internal -> kzg -> kzg_verify.go -> NewVerify](https://github.com/sytansy/go-kzg-4844/blob/389d29f6c57d1c384ad9f7dd14489304111c1a56/internal/kzg/kzg_verify.go#L101)
- [internal -> kzg -> kzg_verify.go -> GnarkVerify](https://github.com/sytansy/go-kzg-4844/blob/389d29f6c57d1c384ad9f7dd14489304111c1a56/internal/kzg/kzg_verify.go#L137) 

The test cases are updated accordingly as well:
- [internal -> kzg -> kzg_verify.go -> TestProofVerifySmoke](https://github.com/sytansy/go-kzg-4844/blob/389d29f6c57d1c384ad9f7dd14489304111c1a56/internal/kzg/kzg_test.go#L12)
- [internal -> kzg -> kzg_verify.go -> TestBatchVerifySmoke](https://github.com/sytansy/go-kzg-4844/blob/389d29f6c57d1c384ad9f7dd14489304111c1a56/internal/kzg/kzg_test.go#L39)


## go-eth-kzg

This library provides the necessary cryptographic functions for EIP-4844. If one
is not familiar with EIP-4844, you can think of this library as a KZG library
where the polynomial degree is set to 4095 and opening proofs are computed on
polynomials in lagrange form (4096 evaluations at 4096'th roots of unity).

## Installation

```
go get github.com/crate-crypto/go-eth-kzg
```

## Example

Check out [`examples_test.go`](./examples_test.go) for an example of how to use
this library.

## Benchmarks

To run the benchmarks, execute the following command:

```
go test -bench=.
```

## Consensus specs

This version of the code is conformant with the consensus-specs as of the
following commit: `017a8495f7671f5fff2075a9bfc9238c1a0982f8`

## Security

- For security bugs in this library, email <kev@the.dev>.
- This library uses
  [gnark-crypto](https://github.com/ConsenSys/gnark-crypto/tree/master) for
  elliptic curve operations. An audit of gnark can be seen
  [here](https://github.com/ConsenSys/gnark-crypto/blob/master/audit_oct2022.pdf).
  This library uses a more recent version than the audited version, since that
  version had a serialization bug.
  We only rely on gnark-crypto's underlying group operations and pairing code
  for bls12-381. For code that we do need to use, that has not been audited, we
  have copied it into this library so that it can be a part of this libraries
  audit. We have noted in the comments which functions we have done this for.
  
### Panics

Panics can be a DoS vector when running code in a node. This library endeavors
to only panic on startup; only methods which are called when we create the
`Context` object should panic.

## Minimum Supported Golang Version

Because we use generics, the minimum golang version needs to be 1.18 or above. Since Golang only back ports security fixes to the latest version and one version behind latest, this library will at most be one version behind latest.

Tests are ran against the current version and the latest version.

## License

This project is licensed under the APACHE-2 license.
