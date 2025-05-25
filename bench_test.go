package goethkzg_test

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"log"
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	bls12381 "github.com/consensys/gnark-crypto/ecc/bls12-381"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	goethkzg "github.com/crate-crypto/go-eth-kzg"
	"github.com/crate-crypto/go-eth-kzg/internal/kzg"
	"github.com/stretchr/testify/require"
)

func deterministicRandomness(seed int64) [32]byte {
	// Converts an int64 to a byte slice
	buf := new(bytes.Buffer)
	err := binary.Write(buf, binary.BigEndian, seed)
	if err != nil {
		log.Fatalf("Failed to write int64 to bytes buffer: %v", err)
	}
	bytes := buf.Bytes()

	return sha256.Sum256(bytes)
}

// Returns a serialized random field element in big-endian
func GetRandFieldElement(seed int64) [32]byte {
	bytes := deterministicRandomness(seed)
	var r fr.Element
	r.SetBytes(bytes[:])

	return goethkzg.SerializeScalar(r)
}

func GetRandBlob(seed int64) *goethkzg.Blob {
	var blob goethkzg.Blob
	bytesPerBlob := goethkzg.ScalarsPerBlob * goethkzg.SerializedScalarSize
	for i := 0; i < bytesPerBlob; i += goethkzg.SerializedScalarSize {
		fieldElementBytes := GetRandFieldElement(seed + int64(i))
		copy(blob[i:i+goethkzg.SerializedScalarSize], fieldElementBytes[:])
	}
	return &blob
}

func BenchmarkPointOperations(b *testing.B) {
	const length = 32
	blobs := make([]goethkzg.Blob, length)
	commitments := make([]goethkzg.KZGCommitment, length)
	//proofs := make([]goethkzg.KZGProof, length)
	fields := make([]goethkzg.Scalar, length)
	A := make([]bls12381.G1Affine, length)
	J := make([]bls12381.G1Jac, length)
	x := make([]fr.Element, length)
	s := make([]big.Int, length)

	var randnum fr.Element
	randnum.SetRandom()
	var num big.Int
	randnum.BigInt(&num)

	seq := make([]fr.Element, length)
	u := make([]big.Int, length)

	for i := 0; i < length; i++ {
		blob := GetRandBlob(int64(i))
		commitment, err := ctx.BlobToKZGCommitment(blob, NumGoRoutines)
		require.NoError(b, err)
		//proof, err := ctx.ComputeBlobKZGProof(blob, commitment, NumGoRoutines)
		//require.NoError(b, err)

		blobs[i] = *blob
		commitments[i] = commitment
		A[i], _ = goethkzg.DeserializeKZGCommitment(commitment)
		J[i].FromAffine(&A[i])
		//proofs[i] = proof
		fields[i] = GetRandFieldElement(int64(i))
		x[i], _ = goethkzg.DeserializeScalar(fields[i])
		x[i].BigInt(&s[i])

		if i == 0 {
			seq[i].SetOne()
		} else {
			seq[i].Add(&seq[i-1], &seq[0])
		}
		seq[i].BigInt(&u[i])
	}

	b.Run("AffineAdd", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			A[0].Add(&A[0], &A[1])
		}
	})

	b.Run("JacobAdd", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			J[0].AddAssign(&J[1])
		}
	})

	b.Run("AffineMultiply", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			A[0].ScalarMultiplication(&A[0], &num)
			//_ = ctx.VerifyKZGProof(commitments[0], fields[0], fields[1], proofs[0])
		}
	})

	b.Run("JacobMultiply", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			J[0].ScalarMultiplication(&J[0], &num)
		}
	})

	b.Run("AffineMulD&A", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			kzg.MulByDoubleAndAdd(&A[0], &num)
		}
	})

	b.Run("AffineMultiplySmall", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			A[0].ScalarMultiplication(&A[0], &u[2])
		}
	})

	b.Run("JacobMultiplySmall", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			J[0].ScalarMultiplication(&J[0], &u[2])
		}
	})

	b.Run("AffineMulD&ASmall", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			kzg.MulByDoubleAndAdd(&A[0], &u[2])
		}
	})

	config := ecc.MultiExpConfig{}
	b.Run("AffineMultiExp", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			A[0].MultiExp(A, x, config)
		}
	})

	b.Run("JacobMultiExp", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			J[0].MultiExp(A, x, config)
		}
	})

	b.Run("AffineMultiMulD&A", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			kzg.MultiMul(A, x)
		}
	})

	b.Run("AffineMultiExpSmall", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			A[0].MultiExp(A, seq, config)
		}
	})

	b.Run("JacobMultiExpSmall", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			J[0].MultiExp(A, seq, config)
		}
	})

	b.Run("AffineMultiMulD&ASmall", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			kzg.MultiMul(A, seq)
		}
	})

	b.Run("AffineMulThenInv", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			A[0].ScalarMultiplication(&A[0], &num)
			A[0].Neg(&A[0])
		}
	})

	b.Run("AffineInvThenMul", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			num.Neg(&num)
			A[0].ScalarMultiplication(&A[0], &num)
		}
	})

	b.Run("JacobMulThenInv", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			J[0].ScalarMultiplication(&J[0], &num)
			J[0].Neg(&J[0])
		}
	})

	b.Run("JacobInvThenMul", func(b *testing.B) {
		b.ReportAllocs()
		for n := 0; n < b.N; n++ {
			num.Neg(&num)
			J[0].ScalarMultiplication(&J[0], &num)
		}
	})
}

func Benchmark(b *testing.B) {
	const length = 1024
	blobs := make([]goethkzg.Blob, length)
	commitments := make([]goethkzg.KZGCommitment, length)
	commitmentsMono := make([]goethkzg.KZGCommitment, length)
	proofs := make([]goethkzg.KZGProof, length)
	fields := make([]goethkzg.Scalar, length)

	for i := 0; i < length; i++ {
		blob := GetRandBlob(int64(i))
		commitment, err := ctx.BlobToKZGCommitment(blob, NumGoRoutines)
		require.NoError(b, err)
		commitmentMono, err := ctx.BlobToKZGCommitmentMonomial(blob, NumGoRoutines)
		require.NoError(b, err)
		proof, err := ctx.ComputeBlobKZGProof(blob, commitment, NumGoRoutines)
		require.NoError(b, err)

		blobs[i] = *blob
		commitments[i] = commitment
		commitmentsMono[i] = commitmentMono
		proofs[i] = proof
		fields[i] = GetRandFieldElement(int64(i))
	}

	///////////////////////////////////////////////////////////////////////////
	// Public functions
	///////////////////////////////////////////////////////////////////////////

	// b.Run("BlobToKZGCommitment", func(b *testing.B) {
	// 	b.ReportAllocs()
	// 	for n := 0; n < b.N; n++ {
	// 		_, _ = ctx.BlobToKZGCommitment(&blobs[0], NumGoRoutines)
	// 	}
	// })

	// b.Run("ComputeKZGProof", func(b *testing.B) {
	// 	b.ReportAllocs()
	// 	for n := 0; n < b.N; n++ {
	// 		_, _, _ = ctx.ComputeKZGProof(&blobs[0], fields[0], NumGoRoutines)
	// 	}
	// })

	// b.Run("ComputeBlobKZGProof", func(b *testing.B) {
	// 	b.ReportAllocs()
	// 	for n := 0; n < b.N; n++ {
	// 		_, _ = ctx.ComputeBlobKZGProof(&blobs[0], commitments[0], NumGoRoutines)
	// 	}
	// })

	// b.Run("VerifyKZGProof", func(b *testing.B) {
	// 	b.ReportAllocs()
	// 	for n := 0; n < b.N; n++ {
	// 		_ = ctx.VerifyKZGProof(commitments[0], fields[0], fields[1], proofs[0])
	// 	}
	// })

	// b.Run("NewVerifyKZGProof", func(b *testing.B) {
	// 	b.ReportAllocs()
	// 	for n := 0; n < b.N; n++ {
	// 		_ = ctx.NewVerifyKZGProof(commitments[0], fields[0], fields[1], proofs[0])
	// 	}
	// })

	// b.Run("GnarkVerifyKZGProof", func(b *testing.B) {
	// 	b.ReportAllocs()
	// 	for n := 0; n < b.N; n++ {
	// 		_ = ctx.GnarkVerifyKZGProof(commitments[0], fields[0], fields[1], proofs[0])
	// 	}
	// })

	// b.Run("VerifyBlobKZGProof", func(b *testing.B) {
	// 	b.ReportAllocs()
	// 	for n := 0; n < b.N; n++ {
	// 		_ = ctx.VerifyBlobKZGProof(&blobs[0], commitments[0], proofs[0])
	// 	}
	// })

	// b.Run("NewVerifyBlobKZGProof", func(b *testing.B) {
	// 	b.ReportAllocs()
	// 	for n := 0; n < b.N; n++ {
	// 		_ = ctx.NewVerifyBlobKZGProof(&blobs[0], commitments[0], proofs[0])
	// 	}
	// })

	// b.Run("GnarkVerifyBlobKZGProof", func(b *testing.B) {
	// 	b.ReportAllocs()
	// 	for n := 0; n < b.N; n++ {
	// 		_ = ctx.GnarkVerifyBlobKZGProof(&blobs[0], commitments[0], proofs[0])
	// 	}
	// })

	// for i := 1; i <= len(blobs); i *= 2 {
	// 	b.Run(fmt.Sprintf("OriBatch(count=%v)", i), func(b *testing.B) {
	// 		commitments, openingProofs, _ := ctx.GenTest(blobs[:i], commitments[:i], proofs[:i])
	// 		b.ReportAllocs()
	// 		for n := 0; n < b.N; n++ {
	// 			_ = ctx.OriTest(commitments, openingProofs)
	// 		}
	// 	})
	// }
	// for i := 1; i <= len(blobs); i *= 2 {
	// 	b.Run(fmt.Sprintf("InvBatch(count=%v)", i), func(b *testing.B) {
	// 		commitments, openingProofs, _ := ctx.GenTest(blobs[:i], commitments[:i], proofs[:i])
	// 		b.ReportAllocs()
	// 		for n := 0; n < b.N; n++ {
	// 			_ = ctx.InvTest(commitments, openingProofs)
	// 		}
	// 	})
	// }
	// for i := 1; i <= len(blobs); i *= 2 {
	// 	b.Run(fmt.Sprintf("NewBatch(count=%v)", i), func(b *testing.B) {
	// 		commitments, openingProofs, _ := ctx.GenTest(blobs[:i], commitments[:i], proofs[:i])
	// 		b.ReportAllocs()
	// 		for n := 0; n < b.N; n++ {
	// 			_ = ctx.NewTest(commitments, openingProofs)
	// 		}
	// 	})
	// }

	// for i := 1; i <= len(blobs); i *= 2 {
	// 	b.Run(fmt.Sprintf("VerifyBlobKZGProofBatch(count=%v)", i), func(b *testing.B) {
	// 		b.ReportAllocs()
	// 		for n := 0; n < b.N; n++ {
	// 			_ = ctx.VerifyBlobKZGProofBatch(blobs[:i], commitments[:i], proofs[:i])
	// 		}
	// 	})
	// }

	// for i := 1; i <= len(blobs); i *= 2 {
	// 	b.Run(fmt.Sprintf("VerifyBlobKZGProofBatchPar(count=%v)", i), func(b *testing.B) {
	// 		b.ReportAllocs()
	// 		for n := 0; n < b.N; n++ {
	// 			_ = ctx.VerifyBlobKZGProofBatchPar(blobs[:i], commitments[:i], proofs[:i])
	// 		}
	// 	})
	// }

	for i := 1; i <= len(blobs); i *= 2 {
		i := i // capture loop variable
		b.Run(fmt.Sprintf("OriBatchVerify(count=%d)", i), func(b *testing.B) {
			
			commitments, Proofs, _ := ctx.GenOriBatchTest(blobs[:i], commitmentsMono[:i], NumGoRoutines)
			b.ReportAllocs()
			for n := 0; n < b.N; n++ {
				_ = ctx.OriSingleTest(commitments, goethkzg.BatchOpeningProof(Proofs))
			}
		})
	}

	for i := 1; i <= len(blobs); i *= 2 {
		i := i // capture loop variable
		b.Run(fmt.Sprintf("BatchVerify(count=%d)", i), func(b *testing.B) {
			
			commitments, Proofs, _ := ctx.OriBatchTest(blobs[:i], commitmentsMono[:i], NumGoRoutines)
			b.ReportAllocs()
			for n := 0; n < b.N; n++ {
				_ = ctx.SingleTest(commitments, goethkzg.BatchOpeningProof(Proofs))
			}
		})
	}
}

func BenchmarkDeserializeBlob(b *testing.B) {
	var (
		blob       = GetRandBlob(int64(13))
		first, err = goethkzg.DeserializeBlob(blob)
		second     kzg.Polynomial
	)
	if err != nil {
		b.Fatal(err)
	}
	b.ResetTimer()
	b.ReportAllocs()
	for n := 0; n < b.N; n++ {
		second, err = goethkzg.DeserializeBlob(blob)
		if err != nil {
			b.Fatal(err)
		}
	}
	if have, want := fmt.Sprintf("%x", second), fmt.Sprintf("%x", first); have != want {
		b.Fatalf("have %s want %s", have, want)
	}
}
