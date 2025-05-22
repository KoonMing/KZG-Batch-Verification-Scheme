package goethkzg

import (
	bls12381 "github.com/consensys/gnark-crypto/ecc/bls12-381"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/crate-crypto/go-eth-kzg/internal/kzg"
	"golang.org/x/sync/errgroup"
)

// BatchOpeningProof is a struct holding a (cryptographic) proof to the claim that multi polynomial f_i(X) (represented by multi
// commitment to them) evaluates at multi points `z_i` to `f_i(z_i)`.
type BatchOpeningProof struct {
	// Commitment to quotient polynomial \sum_{i=1}^k (f_i(X) - f_i(z_i))/(X-z_i)
	QuotientCommitmentW bls12381.G1Affine

	// Commitment to quotient polynomial \sum_{i=1}^k (f_i(X) - f_i(z_i))/(t-z_i)(X-z_i)
	QuotientCommitmentX bls12381.G1Affine

	// Point that we are evaluating the polynomial at : `z_i`
	InputPoint []fr.Element

	// ClaimedValue purported value : `f(z)`
	ClaimedValue []fr.Element
}

// VerifyKZGProof implements [verify_kzg_proof].
//
// [verify_kzg_proof]: https://github.com/ethereum/consensus-specs/blob/017a8495f7671f5fff2075a9bfc9238c1a0982f8/specs/deneb/polynomial-commitments.md#verify_kzg_proof
func (c *Context) VerifyKZGProof(blobCommitment KZGCommitment, inputPointBytes, claimedValueBytes Scalar, kzgProof KZGProof) error {
	// 1. Deserialization
	//
	claimedValue, err := DeserializeScalar(claimedValueBytes)
	if err != nil {
		return err
	}

	inputPoint, err := DeserializeScalar(inputPointBytes)
	if err != nil {
		return err
	}

	polynomialCommitment, err := DeserializeKZGCommitment(blobCommitment)
	if err != nil {
		return err
	}

	quotientCommitment, err := DeserializeKZGProof(kzgProof)
	if err != nil {
		return err
	}

	// 2. Verify opening proof
	proof := kzg.OpeningProof{
		QuotientCommitment: quotientCommitment,
		InputPoint:         inputPoint,
		ClaimedValue:       claimedValue,
	}

	return kzg.Verify(&polynomialCommitment, &proof, c.openKey)
}

func (c *Context) NewVerifyKZGProof(blobCommitment KZGCommitment, inputPointBytes, claimedValueBytes Scalar, kzgProof KZGProof) error {
	// 1. Deserialization
	//
	claimedValue, err := DeserializeScalar(claimedValueBytes)
	if err != nil {
		return err
	}

	inputPoint, err := DeserializeScalar(inputPointBytes)
	if err != nil {
		return err
	}

	polynomialCommitment, err := DeserializeKZGCommitment(blobCommitment)
	if err != nil {
		return err
	}

	quotientCommitment, err := DeserializeKZGProof(kzgProof)
	if err != nil {
		return err
	}

	// 2. Verify opening proof
	proof := kzg.OpeningProof{
		QuotientCommitment: quotientCommitment,
		InputPoint:         inputPoint,
		ClaimedValue:       claimedValue,
	}

	return kzg.NewVerify(&polynomialCommitment, &proof, c.openKey)
}

func (c *Context) GnarkVerifyKZGProof(blobCommitment KZGCommitment, inputPointBytes, claimedValueBytes Scalar, kzgProof KZGProof) error {
	// 1. Deserialization
	//
	claimedValue, err := DeserializeScalar(claimedValueBytes)
	if err != nil {
		return err
	}

	inputPoint, err := DeserializeScalar(inputPointBytes)
	if err != nil {
		return err
	}

	polynomialCommitment, err := DeserializeKZGCommitment(blobCommitment)
	if err != nil {
		return err
	}

	quotientCommitment, err := DeserializeKZGProof(kzgProof)
	if err != nil {
		return err
	}

	// 2. Verify opening proof
	proof := kzg.OpeningProof{
		QuotientCommitment: quotientCommitment,
		InputPoint:         inputPoint,
		ClaimedValue:       claimedValue,
	}

	return kzg.GnarkVerify(&polynomialCommitment, &proof, c.openKey)
}

// VerifyBlobKZGProof implements [verify_blob_kzg_proof].
//
// [verify_blob_kzg_proof]: https://github.com/ethereum/consensus-specs/blob/017a8495f7671f5fff2075a9bfc9238c1a0982f8/specs/deneb/polynomial-commitments.md#verify_blob_kzg_proof
func (c *Context) VerifyBlobKZGProof(blob *Blob, blobCommitment KZGCommitment, kzgProof KZGProof) error {
	// 1. Deserialize
	//
	polynomial, err := DeserializeBlob(blob)
	if err != nil {
		return err
	}

	polynomialCommitment, err := DeserializeKZGCommitment(blobCommitment)
	if err != nil {
		return err
	}

	quotientCommitment, err := DeserializeKZGProof(kzgProof)
	if err != nil {
		return err
	}

	// 2. Compute the evaluation challenge
	evaluationChallenge := computeChallenge(blob, blobCommitment)

	// 3. Compute output point/ claimed value
	outputPoint, err := c.domain.EvaluateLagrangePolynomial(polynomial, evaluationChallenge)
	if err != nil {
		return err
	}

	// 4. Verify opening proof
	openingProof := kzg.OpeningProof{
		QuotientCommitment: quotientCommitment,
		InputPoint:         evaluationChallenge,
		ClaimedValue:       *outputPoint,
	}

	return kzg.Verify(&polynomialCommitment, &openingProof, c.openKey)
}

func (c *Context) NewVerifyBlobKZGProof(blob *Blob, blobCommitment KZGCommitment, kzgProof KZGProof) error {
	// 1. Deserialize
	//
	polynomial, err := DeserializeBlob(blob)
	if err != nil {
		return err
	}

	polynomialCommitment, err := DeserializeKZGCommitment(blobCommitment)
	if err != nil {
		return err
	}

	quotientCommitment, err := DeserializeKZGProof(kzgProof)
	if err != nil {
		return err
	}

	// 2. Compute the evaluation challenge
	evaluationChallenge := computeChallenge(blob, blobCommitment)

	// 3. Compute output point/ claimed value
	outputPoint, err := c.domain.EvaluateLagrangePolynomial(polynomial, evaluationChallenge)
	if err != nil {
		return err
	}

	// 4. Verify opening proof
	openingProof := kzg.OpeningProof{
		QuotientCommitment: quotientCommitment,
		InputPoint:         evaluationChallenge,
		ClaimedValue:       *outputPoint,
	}

	return kzg.NewVerify(&polynomialCommitment, &openingProof, c.openKey)
}

func (c *Context) GnarkVerifyBlobKZGProof(blob *Blob, blobCommitment KZGCommitment, kzgProof KZGProof) error {
	// 1. Deserialize
	//
	polynomial, err := DeserializeBlob(blob)
	if err != nil {
		return err
	}

	polynomialCommitment, err := DeserializeKZGCommitment(blobCommitment)
	if err != nil {
		return err
	}

	quotientCommitment, err := DeserializeKZGProof(kzgProof)
	if err != nil {
		return err
	}

	// 2. Compute the evaluation challenge
	evaluationChallenge := computeChallenge(blob, blobCommitment)

	// 3. Compute output point/ claimed value
	outputPoint, err := c.domain.EvaluateLagrangePolynomial(polynomial, evaluationChallenge)
	if err != nil {
		return err
	}

	// 4. Verify opening proof
	openingProof := kzg.OpeningProof{
		QuotientCommitment: quotientCommitment,
		InputPoint:         evaluationChallenge,
		ClaimedValue:       *outputPoint,
	}

	return kzg.GnarkVerify(&polynomialCommitment, &openingProof, c.openKey)
}

// VerifyBlobKZGProofBatch implements [verify_blob_kzg_proof_batch].
//
// [verify_blob_kzg_proof_batch]: https://github.com/ethereum/consensus-specs/blob/017a8495f7671f5fff2075a9bfc9238c1a0982f8/specs/deneb/polynomial-commitments.md#verify_blob_kzg_proof_batch
func (c *Context) VerifyBlobKZGProofBatch(blobs []Blob, polynomialCommitments []KZGCommitment, kzgProofs []KZGProof) error {
	// 1. Check that all components in the batch have the same size
	//
	blobsLen := len(blobs)
	lengthsAreEqual := blobsLen == len(polynomialCommitments) && blobsLen == len(kzgProofs)
	if !lengthsAreEqual {
		return ErrBatchLengthCheck
	}
	batchSize := blobsLen

	// 2. Collect opening proofs
	//
	openingProofs := make([]kzg.OpeningProof, batchSize)
	commitments := make([]bls12381.G1Affine, batchSize)
	for i := 0; i < batchSize; i++ {
		// 2a. Deserialize
		//
		serComm := polynomialCommitments[i]
		polynomialCommitment, err := DeserializeKZGCommitment(serComm)
		if err != nil {
			return err
		}

		kzgProof := kzgProofs[i]
		quotientCommitment, err := DeserializeKZGProof(kzgProof)
		if err != nil {
			return err
		}

		blob := &blobs[i]
		polynomial, err := DeserializeBlob(blob)
		if err != nil {
			return err
		}

		// 2b. Compute the evaluation challenge
		evaluationChallenge := computeChallenge(blob, serComm)

		// 2c. Compute output point/ claimed value
		outputPoint, err := c.domain.EvaluateLagrangePolynomial(polynomial, evaluationChallenge)
		if err != nil {
			return err
		}

		// 2d. Append opening proof to list
		openingProof := kzg.OpeningProof{
			QuotientCommitment: quotientCommitment,
			InputPoint:         evaluationChallenge,
			ClaimedValue:       *outputPoint,
		}
		openingProofs[i] = openingProof
		commitments[i] = polynomialCommitment
	}

	// 3. Verify opening proofs
	return kzg.BatchVerifyMultiPoints(commitments, openingProofs, c.openKey)
}

func (c *Context) GenTest(blobs []Blob, polynomialCommitments []KZGCommitment, kzgProofs []KZGProof) ([]bls12381.G1Affine, []kzg.OpeningProof, error) {
	// 1. Check that all components in the batch have the same size
	//
	blobsLen := len(blobs)
	lengthsAreEqual := blobsLen == len(polynomialCommitments) && blobsLen == len(kzgProofs)
	if !lengthsAreEqual {
		return nil, nil, ErrBatchLengthCheck
	}
	batchSize := blobsLen

	// 2. Collect opening proofs
	//
	openingProofs := make([]kzg.OpeningProof, batchSize)
	commitments := make([]bls12381.G1Affine, batchSize)
	for i := 0; i < batchSize; i++ {
		// 2a. Deserialize
		//
		serComm := polynomialCommitments[i]
		polynomialCommitment, err := DeserializeKZGCommitment(serComm)
		if err != nil {
			return nil, nil, err
		}

		kzgProof := kzgProofs[i]
		quotientCommitment, err := DeserializeKZGProof(kzgProof)
		if err != nil {
			return nil, nil, err
		}

		blob := &blobs[i]
		polynomial, err := DeserializeBlob(blob)
		if err != nil {
			return nil, nil, err
		}

		// 2b. Compute the evaluation challenge
		evaluationChallenge := computeChallenge(blob, serComm)

		// 2c. Compute output point/ claimed value
		outputPoint, err := c.domain.EvaluateLagrangePolynomial(polynomial, evaluationChallenge)
		if err != nil {
			return nil, nil, err
		}

		// 2d. Append opening proof to list
		openingProof := kzg.OpeningProof{
			QuotientCommitment: quotientCommitment,
			InputPoint:         evaluationChallenge,
			ClaimedValue:       *outputPoint,
		}
		openingProofs[i] = openingProof
		commitments[i] = polynomialCommitment
	}

	return commitments, openingProofs, nil
}

func (c *Context) GenBatchTest(blobs []Blob, polynomialCommitments []KZGCommitment, numGoRoutines int) ([]bls12381.G1Affine, kzg.BatchOpeningProof, error) {
	blobsLen := len(blobs)
	batchSize := blobsLen

	polynomials := make([]kzg.Polynomial, batchSize)
	z := make([]fr.Element, batchSize)
	commitments := make([]bls12381.G1Affine, batchSize)

	for i := 0; i < batchSize; i++ {
		// 2a. Deserialize
		//
		serComm := polynomialCommitments[i]
		polynomialCommitment, err := DeserializeKZGCommitment(serComm)
		if err != nil {
			return nil, kzg.BatchOpeningProof{}, err
		}

		blob := &blobs[i]
		polynomial, err := DeserializeBlob(blob)
		if err != nil {
			return nil, kzg.BatchOpeningProof{}, err
		}
		polynomials[i] = polynomial

		// 2b. Compute the evaluation challenge
		evaluationChallenge := computeChallenge(blob, serComm)
		z[i] = evaluationChallenge

		commitments[i] = polynomialCommitment
	}

	proof, err := kzg.OriBatchOpen(commitments, polynomials, z, c.commitKeyMonomial, numGoRoutines)
	if err != nil {
		return nil, kzg.BatchOpeningProof{}, err
	}
	return commitments, proof, nil
}

func (c *Context) OriTest(commitments []bls12381.G1Affine, openingProofs []kzg.OpeningProof) error {
	return kzg.BatchVerifyMultiPoints(commitments, openingProofs, c.openKey)
}

func (c *Context) InvTest(commitments []bls12381.G1Affine, openingProofs []kzg.OpeningProof) error {
	return kzg.InvBatchVerifyMultiPoints(commitments, openingProofs, c.openKey)
}

func (c *Context) NewTest(commitments []bls12381.G1Affine, openingProofs []kzg.OpeningProof) error {
	return kzg.NewBatchVerifyMultiPoints(commitments, openingProofs, c.openKey)
}

func (c *Context) OriSingleTest(commitments []bls12381.G1Affine, openingProofs BatchOpeningProof) error {
	// Convert local BatchOpeningProof to kzg.BatchOpeningProof
	kzgOpeningProofs := kzg.BatchOpeningProof{
		QuotientCommitmentW: openingProofs.QuotientCommitmentW,
		QuotientCommitmentX: openingProofs.QuotientCommitmentX,
		InputPoint:          openingProofs.InputPoint,
		ClaimedValue:        openingProofs.ClaimedValue,
	}
	return kzg.OriBatchVerify(commitments, kzgOpeningProofs, c.openKey)
}

// VerifyBlobKZGProofBatchPar implements [verify_blob_kzg_proof_batch]. This is the parallelized version of
// [Context.VerifyBlobKZGProofBatch], which is single-threaded. This function uses go-routines to process each proof in
// parallel. If you are worried about resource starvation on large batches, it is advised to schedule your own
// go-routines in a more intricate way than done below for large batches.
//
// [verify_blob_kzg_proof_batch]: https://github.com/ethereum/consensus-specs/blob/017a8495f7671f5fff2075a9bfc9238c1a0982f8/specs/deneb/polynomial-commitments.md#verify_blob_kzg_proof_batch
func (c *Context) VerifyBlobKZGProofBatchPar(blobs []Blob, commitments []KZGCommitment, proofs []KZGProof) error {
	// 1. Check that all components in the batch have the same size
	if len(commitments) != len(blobs) || len(proofs) != len(blobs) {
		return ErrBatchLengthCheck
	}

	// 2. Verify each opening proof using green threads
	var errG errgroup.Group
	for i := range blobs {
		j := i // Capture the value of the loop variable
		errG.Go(func() error {
			return c.VerifyBlobKZGProof(&blobs[j], commitments[j], proofs[j])
		})
	}

	// 3. Wait for all go routines to complete and check if any returned an error
	return errG.Wait()
}
