package kzg

import (
	"math/big"
	"math/rand"

	"github.com/consensys/gnark-crypto/ecc"
	bls12381 "github.com/consensys/gnark-crypto/ecc/bls12-381"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/crate-crypto/go-eth-kzg/internal/utils"
)

// OpeningProof is a struct holding a (cryptographic) proof to the claim that a polynomial f(X) (represented by a
// commitment to it) evaluates at a point `z` to `f(z)`.
type OpeningProof struct {
	// Commitment to quotient polynomial (f(X) - f(z))/(X-z)
	QuotientCommitment bls12381.G1Affine

	// Point that we are evaluating the polynomial at : `z`
	InputPoint fr.Element

	// ClaimedValue purported value : `f(z)`
	ClaimedValue fr.Element
}

// Verify a single KZG proof. See [verify_kzg_proof_impl]. Returns `nil` if verification was successful, an error
// otherwise. If verification failed due to the pairings check it will return [ErrVerifyOpeningProof].
//
// Note: We could make this method faster by storing pre-computations for the generators in G1 and G2
// as we only do scalar multiplications with those in this method.
//
// Modified from [gnark-crypto].
//
// [verify_kzg_proof_impl]: https://github.com/ethereum/consensus-specs/blob/017a8495f7671f5fff2075a9bfc9238c1a0982f8/specs/deneb/polynomial-commitments.md#verify_kzg_proof_impl
// [gnark-crypto]: https://github.com/ConsenSys/gnark-crypto/blob/8f7ca09273c24ed9465043566906cbecf5dcee91/ecc/bls12-381/fr/kzg/kzg.go#L166
func Verify(commitment *Commitment, proof *OpeningProof, openKey *OpeningKey) error {
	// [-1]G₂
	// It's possible to precompute this, however Negation
	// is cheap (2 Fp negations), so doing it per verify
	// should be insignificant compared to the rest of Verify.
	var negG2 bls12381.G2Affine
	negG2.Neg(&openKey.GenG2)

	// Convert the G2 generator to Jacobian for
	// later computations.
	var genG2Jac bls12381.G2Jac
	genG2Jac.FromAffine(&openKey.GenG2)

	// This has been changed slightly from the way that gnark-crypto
	// does it to show the symmetry in the computation required for
	// G₂ and G₁. This is the way it is done in the specs.

	// [z]G₂
	var inputPointG2Jac bls12381.G2Jac
	var pointBigInt big.Int
	proof.InputPoint.BigInt(&pointBigInt)
	inputPointG2Jac.ScalarMultiplication(&genG2Jac, &pointBigInt)

	// In the specs, this is denoted as `X_minus_z`
	//
	// [α - z]G₂
	var alphaMinusZG2Jac bls12381.G2Jac
	alphaMinusZG2Jac.FromAffine(&openKey.AlphaG2)
	alphaMinusZG2Jac.SubAssign(&inputPointG2Jac)

	// [α-z]G₂ (Convert to Affine format)
	var alphaMinusZG2Aff bls12381.G2Affine
	alphaMinusZG2Aff.FromJacobian(&alphaMinusZG2Jac)

	// [f(z)]G₁
	var claimedValueG1Jac bls12381.G1Jac
	var claimedValueBigInt big.Int
	proof.ClaimedValue.BigInt(&claimedValueBigInt)
	claimedValueG1Jac.ScalarMultiplicationAffine(&openKey.GenG1, &claimedValueBigInt)

	//  In the specs, this is denoted as `P_minus_y`
	//
	// [f(α) - f(z)]G₁
	var fminusfzG1Jac bls12381.G1Jac
	fminusfzG1Jac.FromAffine(commitment)
	fminusfzG1Jac.SubAssign(&claimedValueG1Jac)

	// [f(α) - f(z)]G₁ (Convert to Affine format)
	var fminusfzG1Aff bls12381.G1Affine
	fminusfzG1Aff.FromJacobian(&fminusfzG1Jac)

	check, err := bls12381.PairingCheck(
		[]bls12381.G1Affine{fminusfzG1Aff, proof.QuotientCommitment},
		[]bls12381.G2Affine{negG2, alphaMinusZG2Aff},
	)
	if err != nil {
		return err
	}
	if !check {
		return ErrVerifyOpeningProof
	}

	return nil
}

func NewVerify(commitment *Commitment, proof *OpeningProof, openKey *OpeningKey) error {
	// [f(z)]G₁
	var claimedValueG1Jac bls12381.G1Jac
	var f_z big.Int
	proof.ClaimedValue.BigInt(&f_z)
	f_z.Neg(&f_z)

	var z big.Int
	proof.InputPoint.BigInt(&z)
	claimedValueG1Jac.JointScalarMultiplicationBase(&proof.QuotientCommitment, &f_z, &z)

	// [f(α) - f(z)]G₁
	var commJac bls12381.G1Jac
	commJac.FromAffine(commitment)
	commJac.AddAssign(&claimedValueG1Jac)

	// -([f(α) - f(z)]G₁ + zW) (Convert to Affine format)
	var secondPairing bls12381.G1Affine
	secondPairing.FromJacobian(&commJac)
	secondPairing.Neg(&secondPairing)

	check, err := bls12381.PairingCheck(
		[]bls12381.G1Affine{secondPairing, proof.QuotientCommitment},
		[]bls12381.G2Affine{openKey.GenG2, openKey.AlphaG2},
	)
	if err != nil {
		return err
	}
	if !check {
		return ErrVerifyOpeningProof
	}

	return nil
}

// This is the gnark-crypto way, which is slightly more efficient.
func GnarkVerify(commitment *Commitment, proof *OpeningProof, openKey *OpeningKey) error {
	// [f(z)]G₁ - [z]W
	var claimedValueG1Jac bls12381.G1Jac

	var claimedValueBigInt big.Int
	proof.ClaimedValue.BigInt(&claimedValueBigInt)

	var pointBigInt big.Int
	proof.InputPoint.BigInt(&pointBigInt)
	pointBigInt.Neg(&pointBigInt)

	claimedValueG1Jac.JointScalarMultiplicationBase(&proof.QuotientCommitment, &claimedValueBigInt, &pointBigInt)

	// [f(z)]G₁ - [z]W - C (Convert to Affine format)
	var commJac bls12381.G1Jac
	commJac.FromAffine(commitment)
	claimedValueG1Jac.SubAssign(&commJac)
	var secondPairing bls12381.G1Affine
	secondPairing.FromJacobian(&claimedValueG1Jac)

	check, err := bls12381.PairingCheck(
		[]bls12381.G1Affine{secondPairing, proof.QuotientCommitment},
		[]bls12381.G2Affine{openKey.GenG2, openKey.AlphaG2},
	)
	if err != nil {
		return err
	}
	if !check {
		return ErrVerifyOpeningProof
	}

	return nil
}

// BatchVerifyMultiPoints verifies multiple KZG proofs in a batch. See [verify_kzg_proof_batch].
//
//   - This method is more efficient than calling [Verify] multiple times.
//   - Randomness is used to combine multiple proofs into one.
//
// Modified from [gnark-crypto].
//
// [verify_kzg_proof_batch]: https://github.com/ethereum/consensus-specs/blob/017a8495f7671f5fff2075a9bfc9238c1a0982f8/specs/deneb/polynomial-commitments.md#verify_kzg_proof_batch
// [gnark-crypto]: https://github.com/ConsenSys/gnark-crypto/blob/8f7ca09273c24ed9465043566906cbecf5dcee91/ecc/bls12-381/fr/kzg/kzg.go#L367)
func BatchVerifyMultiPoints(commitments []Commitment, proofs []OpeningProof, openKey *OpeningKey) error {
	// Check consistency number of proofs is equal to the number of commitments.
	if len(commitments) != len(proofs) {
		return ErrInvalidNumDigests
	}
	batchSize := len(commitments)

	// If there is nothing to verify, we return nil
	// to signal that verification was true.
	//
	if batchSize == 0 {
		return nil
	}

	// If batch size is `1`, call Verify
	if batchSize == 1 {
		return Verify(&commitments[0], &proofs[0], openKey)
	}

	// Sample random numbers for sampling.
	//
	// We only need to sample one random number and
	// compute powers of that random number. This works
	// since powers will produce a vandermonde matrix
	// which is linearly independent.
	var randomNumber fr.Element
	_, err := randomNumber.SetRandom()
	if err != nil {
		return err
	}
	randomNumbers := utils.ComputePowers(randomNumber, uint(batchSize))

	// Combine random_i*quotient_i
	var foldedQuotients bls12381.G1Affine
	quotients := make([]bls12381.G1Affine, len(proofs))
	for i := 0; i < batchSize; i++ {
		quotients[i].Set(&proofs[i].QuotientCommitment)
	}
	config := ecc.MultiExpConfig{}
	_, err = foldedQuotients.MultiExp(quotients, randomNumbers, config)
	if err != nil {
		return err
	}

	// Fold commitments and evaluations using randomness
	evaluations := make([]fr.Element, batchSize)
	for i := 0; i < len(randomNumbers); i++ {
		evaluations[i].Set(&proofs[i].ClaimedValue)
	}
	foldedCommitments, foldedEvaluations, err := fold(commitments, evaluations, randomNumbers)
	if err != nil {
		return err
	}

	// Compute commitment to folded Eval
	var foldedEvaluationsCommit bls12381.G1Affine
	var foldedEvaluationsBigInt big.Int
	foldedEvaluations.BigInt(&foldedEvaluationsBigInt)
	foldedEvaluationsCommit.ScalarMultiplication(&openKey.GenG1, &foldedEvaluationsBigInt)

	// Compute F = foldedCommitments - foldedEvaluationsCommit
	foldedCommitments.Sub(&foldedCommitments, &foldedEvaluationsCommit)

	// Combine random_i*(point_i*quotient_i)
	var foldedPointsQuotients bls12381.G1Affine
	for i := 0; i < batchSize; i++ {
		randomNumbers[i].Mul(&randomNumbers[i], &proofs[i].InputPoint)
	}
	_, err = foldedPointsQuotients.MultiExp(quotients, randomNumbers, config)
	if err != nil {
		return err
	}

	// `lhs` first pairing
	foldedCommitments.Add(&foldedCommitments, &foldedPointsQuotients)

	// `lhs` second pairing
	foldedQuotients.Neg(&foldedQuotients)

	check, err := bls12381.PairingCheck(
		[]bls12381.G1Affine{foldedCommitments, foldedQuotients},
		[]bls12381.G2Affine{openKey.GenG2, openKey.AlphaG2},
	)
	if err != nil {
		return err
	}
	if !check {
		return ErrVerifyOpeningProof
	}

	return nil
}

/*
	func TempBatchVerifyMultiPoints(commitments []Commitment, proofs []OpeningProof, openKey *OpeningKey) error {
		// Check consistency number of proofs is equal to the number of commitments.
		if len(commitments) != len(proofs) {
			return ErrInvalidNumDigests
		}
		batchSize := len(commitments)

		// If there is nothing to verify, we return nil
		// to signal that verification was true.
		//
		if batchSize == 0 {
			return nil
		}

		// If batch size is `1`, call Verify
		if batchSize == 1 {
			return NewVerify(&commitments[0], &proofs[0], openKey)
		}

		// Sample a random number for sampling.
		//
		// We only need to sample one random number and
		// compute a (aritmetic) sequence of that random number. This works
		// since it resemble a set commitment structure
		// which is also a batch verifier. See
		// [Efficient Fork-Free BLS Multi-Signature Scheme with Incremental Signing]
		var randomNumber fr.Element
		randomNumber.SetInt64(rand.Int63())

		scalars := make([]fr.Element, batchSize)
		seq := make([]fr.Element, batchSize)
		seq[0].SetOne()
		for i := 1; i < batchSize; i++ {
			seq[i].Add(&seq[i-1], &seq[0])
			scalars[i].SetOne()
		}

		//=========2nd pairing starts
		// W = \prod W_i
		var temp1, temp2 bls12381.G1Jac
		var foldedQuotients bls12381.G1Affine
		quotients := make([]bls12381.G1Affine, len(proofs))
		for i := 0; i < batchSize; i++ {
			quotients[i].Set(&proofs[i].QuotientCommitment)
		}
		config := ecc.MultiExpConfig{}
		_, err := temp2.MultiExp(quotients, scalars, config)
		if err != nil {
			return err
		}
		// rW
		var r big.Int
		randomNumber.BigInt(&r)
		temp2.ScalarMultiplication(&temp2, &r)

		// + \prod iW_i
		_, err = temp1.MultiExp(quotients, seq, config)
		if err != nil {
			return err
		}
		temp2.AddAssign(&temp1)
		foldedQuotients.FromJacobian(&temp2)
		//========2nd pairing ends

		//========1st pairing starts
		// \sum C_i
		_, err = temp2.MultiExp(commitments, scalars, config)
		if err != nil {
			return err
		}

		bases := make([]bls12381.G1Affine, (2*batchSize)+2)
		scalars = make([]fr.Element, (2*batchSize)+2)
		var foldedEvaluations fr.Element
		evaluations := make([]fr.Element, batchSize)

		for i := 0; i < batchSize; i++ {
			// r_i = (r + i)
			evaluations[i].Add(&randomNumber, &seq[i])

			//r_i*(z_i)
			scalars[i+batchSize].Mul(&evaluations[i], &proofs[i].InputPoint)

			//\sum r_i*f(z_i)
			evaluations[i].Mul(&evaluations[i], &proofs[i].ClaimedValue)
			foldedEvaluations.Add(&foldedEvaluations, &evaluations[i])

			bases[i].Set(&commitments[i])
			bases[i+batchSize].Set(&quotients[i])
			scalars[i].Set(&seq[i])
		}

		bases[len(bases)-2].FromJacobian(&temp2)
		bases[len(bases)-1].Set(&openKey.GenG1)

		scalars[len(bases)-2].Set(&randomNumber)
		foldedEvaluations.Neg(&foldedEvaluations)
		scalars[len(bases)-1].Set(&foldedEvaluations)

		// `lhs` first pairing
		var foldedCommitments bls12381.G1Affine
		_, err = foldedCommitments.MultiExp(bases, scalars, config)
		if err != nil {
			return err
		}

		// `lhs` second pairing
		foldedQuotients.Neg(&foldedQuotients)

		check, err := bls12381.PairingCheck(
			[]bls12381.G1Affine{foldedCommitments, foldedQuotients},
			[]bls12381.G2Affine{openKey.GenG2, openKey.AlphaG2},
		)
		if err != nil {
			return err
		}
		if !check {
			return ErrVerifyOpeningProof
		}

		return nil
	}
*/
func NewBatchVerifyMultiPoints(commitments []Commitment, proofs []OpeningProof, openKey *OpeningKey) error {
	// Check consistency number of proofs is equal to the number of commitments.
	if len(commitments) != len(proofs) {
		return ErrInvalidNumDigests
	}
	batchSize := len(commitments)

	// If there is nothing to verify, we return nil
	// to signal that verification was true.
	//
	if batchSize == 0 {
		return nil
	}

	// If batch size is `1`, call Verify
	if batchSize == 1 {
		return NewVerify(&commitments[0], &proofs[0], openKey)
	}

	// Sample a random number for sampling.
	//
	// We only need to sample one random number and
	// compute a (aritmetic) sequence of that random number. This works
	// since it resemble a set commitment structure
	// which is also a batch verifier. See
	// [Efficient Fork-Free BLS Multi-Signature Scheme with Incremental Signing]
	var randomNumber fr.Element
	randomNumber.SetInt64(rand.Int63())

	seq := make([]fr.Element, uint(batchSize))
	seq[0].SetOne()
	for i := 1; i < len(seq); i++ {
		seq[i].Add(&seq[i-1], &seq[0])
	}

	allone := make([]fr.Element, uint(batchSize))
	for i := 0; i < len(allone); i++ {
		allone[i].SetOne()
	}

	//=========2nd pairing starts
	// W = \prod W_i
	var temp1, temp2 bls12381.G1Jac
	var foldedQuotients bls12381.G1Affine
	quotients := make([]bls12381.G1Affine, len(proofs))
	for i := 0; i < batchSize; i++ {
		quotients[i].Set(&proofs[i].QuotientCommitment)
	}
	config := ecc.MultiExpConfig{}
	_, err := temp2.MultiExp(quotients, allone, config)
	if err != nil {
		return err
	}
	// rW
	var r big.Int
	randomNumber.BigInt(&r)
	temp2.ScalarMultiplication(&temp2, &r)

	// + \prod iW_i
	_, err = temp1.MultiExp(quotients, seq, config)
	if err != nil {
		return err
	}
	temp2.AddAssign(&temp1)
	foldedQuotients.FromJacobian(&temp2)
	//========2nd pairing ends

	//========1st pairing starts
	// \prod i(C_i), z = \sum p(z_i)(r + i)
	evaluations := make([]fr.Element, batchSize)
	for i := 0; i < len(seq); i++ {
		evaluations[i].Set(&proofs[i].ClaimedValue)
	}
	foldedCommitments, foldedEvaluations, err := newfold(commitments, evaluations, randomNumber, seq)
	if err != nil {
		return err
	}

	// \sum C_i
	_, err = temp2.MultiExp(commitments, allone, config)
	if err != nil {
		return err
	}
	// r(\sum C_i)
	temp2.ScalarMultiplication(&temp2, &r)

	// R = zG
	var foldedEvaluationsBigInt big.Int
	foldedEvaluations.BigInt(&foldedEvaluationsBigInt)
	temp1.FromAffine(&openKey.GenG1)
	temp1.ScalarMultiplication(&temp1, &foldedEvaluationsBigInt)

	// r(\sum C_i) - R
	temp2.SubAssign(&temp1)

	// r(\sum C_i) + \prod i(C_i) - R
	temp1.FromAffine(&foldedCommitments)
	temp2.AddAssign(&temp1)

	// Combine r_i*(z_i)
	//var foldedPointsQuotients bls12381.G1Affine
	for i := 0; i < batchSize; i++ {
		seq[i].Add(&seq[i], &randomNumber)
		seq[i].Mul(&seq[i], &proofs[i].InputPoint)
	}

	_, err = temp1.MultiExp(quotients, seq, config)
	if err != nil {
		return err
	}

	// `lhs` first pairing
	//temp1.FromAffine(&foldedPointsQuotients)
	temp2.AddAssign(&temp1)
	foldedCommitments.FromJacobian(&temp2)

	// `lhs` second pairing
	foldedQuotients.Neg(&foldedQuotients)

	check, err := bls12381.PairingCheck(
		[]bls12381.G1Affine{foldedCommitments, foldedQuotients},
		[]bls12381.G2Affine{openKey.GenG2, openKey.AlphaG2},
	)
	if err != nil {
		return err
	}
	if !check {
		return ErrVerifyOpeningProof
	}

	return nil
}

func InvBatchVerifyMultiPoints(commitments []Commitment, proofs []OpeningProof, openKey *OpeningKey) error {
	// Check consistency number of proofs is equal to the number of commitments.
	if len(commitments) != len(proofs) {
		return ErrInvalidNumDigests
	}
	batchSize := len(commitments)

	// If there is nothing to verify, we return nil
	// to signal that verification was true.
	//
	if batchSize == 0 {
		return nil
	}

	// If batch size is `1`, call Verify
	if batchSize == 1 {
		return Verify(&commitments[0], &proofs[0], openKey)
	}

	// Sample random numbers for sampling.
	//
	// We only need to sample one random number and
	// compute powers of that random number. This works
	// since powers will produce a vandermonde matrix
	// which is linearly independent.
	//var randomNumber fr.Element
	//_, err := randomNumber.SetRandom()
	//if err != nil {
	//	return err
	//}
	//randomNumbers := utils.ComputePowers(randomNumber, uint(batchSize))
	randomNumbers := make([]fr.Element, batchSize)
	for i := 0; i < batchSize; i++ {
		randomNumbers[i].Inverse(&proofs[i].InputPoint)
	}

	// Combine random_i*quotient_i
	var foldedQuotients bls12381.G1Affine
	quotients := make([]bls12381.G1Affine, len(proofs))
	for i := 0; i < batchSize; i++ {
		quotients[i].Set(&proofs[i].QuotientCommitment)
	}
	config := ecc.MultiExpConfig{}
	_, err := foldedQuotients.MultiExp(quotients, randomNumbers, config)
	if err != nil {
		return err
	}

	// Fold commitments and evaluations using randomness
	evaluations := make([]fr.Element, batchSize)
	for i := 0; i < len(randomNumbers); i++ {
		evaluations[i].Set(&proofs[i].ClaimedValue)
	}
	foldedCommitments, foldedEvaluations, err := fold(commitments, evaluations, randomNumbers)
	if err != nil {
		return err
	}

	// Compute commitment to folded Eval
	var foldedEvaluationsCommit bls12381.G1Affine
	var foldedEvaluationsBigInt big.Int
	foldedEvaluations.BigInt(&foldedEvaluationsBigInt)
	foldedEvaluationsCommit.ScalarMultiplication(&openKey.GenG1, &foldedEvaluationsBigInt)

	// Compute F = foldedCommitments - foldedEvaluationsCommit
	foldedCommitments.Sub(&foldedCommitments, &foldedEvaluationsCommit)

	// Combine random_i*(point_i*quotient_i)
	var foldedPointsQuotients bls12381.G1Affine
	for i := 0; i < batchSize; i++ {
		//randomNumbers[i].Mul(&randomNumbers[i], &proofs[i].InputPoint)
		randomNumbers[i].SetOne()
	}
	_, err = foldedPointsQuotients.MultiExp(quotients, randomNumbers, config)
	if err != nil {
		return err
	}

	// `lhs` first pairing
	foldedCommitments.Add(&foldedCommitments, &foldedPointsQuotients)

	// `lhs` second pairing
	foldedQuotients.Neg(&foldedQuotients)

	check, err := bls12381.PairingCheck(
		[]bls12381.G1Affine{foldedCommitments, foldedQuotients},
		[]bls12381.G2Affine{openKey.GenG2, openKey.AlphaG2},
	)
	if err != nil {
		return err
	}
	if !check {
		return ErrVerifyOpeningProof
	}

	return nil
}

// fold computes two inner products with the same factors:
//
//   - Between commitments and factors; This is a multi-exponentiation.
//   - Between evaluations and factors; This is a dot product.
//
// Modified slightly from [gnark-crypto].
//
// [gnark-crypto]: https://github.com/ConsenSys/gnark-crypto/blob/8f7ca09273c24ed9465043566906cbecf5dcee91/ecc/bls12-381/fr/kzg/kzg.go#L464
func fold(commitments []Commitment, evaluations, factors []fr.Element) (Commitment, fr.Element, error) {
	// Length inconsistency between commitments and evaluations should have been done before calling this function
	batchSize := len(commitments)

	// Fold the claimed values
	var foldedEvaluations, tmp fr.Element
	for i := 0; i < batchSize; i++ {
		tmp.Mul(&evaluations[i], &factors[i])
		foldedEvaluations.Add(&foldedEvaluations, &tmp)
	}

	// Fold the commitments
	var foldedCommitments Commitment
	_, err := foldedCommitments.MultiExp(commitments, factors, ecc.MultiExpConfig{})

	if err != nil {
		return foldedCommitments, foldedEvaluations, err
	}

	return foldedCommitments, foldedEvaluations, nil
}

/*
func tempfold(commitments []Commitment, evaluations []fr.Element, randomNumber fr.Element, factors []fr.Element) (Commitment, fr.Element, error) {
	// Length inconsistency between commitments and evaluations should have been done before calling this function
	batchSize := len(commitments)

	// Fold the claimed values
	var foldedEvaluations, tmp fr.Element
	for i := 0; i < batchSize; i++ {
		tmp.Add(&randomNumber, &factors[i])
		tmp.Mul(&evaluations[i], &tmp)
		foldedEvaluations.Add(&foldedEvaluations, &tmp)
	}

	// Fold the commitments
	var foldedCommitments Commitment
	foldedCommitments.FromJacobian(MultiMul(commitments, factors))

	return foldedCommitments, foldedEvaluations, nil
}*/

func newfold(commitments []Commitment, evaluations []fr.Element, randomNumber fr.Element, factors []fr.Element) (Commitment, fr.Element, error) {
	// Length inconsistency between commitments and evaluations should have been done before calling this function
	batchSize := len(commitments)

	// Fold the claimed values
	var foldedEvaluations, tmp fr.Element
	for i := 0; i < batchSize; i++ {
		tmp.Add(&randomNumber, &factors[i])
		tmp.Mul(&evaluations[i], &tmp)
		foldedEvaluations.Add(&foldedEvaluations, &tmp)
	}

	// Fold the commitments
	var foldedCommitments Commitment
	_, err := foldedCommitments.MultiExp(commitments, factors, ecc.MultiExpConfig{})

	if err != nil {
		return foldedCommitments, foldedEvaluations, err
	}

	return foldedCommitments, foldedEvaluations, nil
}

func MultiMul(point []bls12381.G1Affine, exponent []fr.Element) *bls12381.G1Jac {
	var temp bls12381.G1Jac
	var num big.Int
	for i := 0; i < len(point); i++ {
		exponent[i].BigInt(&num)
		temp.AddAssign(MulByDoubleAndAdd(&point[i], &num))
	}

	return &temp
}

func MulByDoubleAndAdd(point *bls12381.G1Affine, exponent *big.Int) *bls12381.G1Jac {
	var result bls12381.G1Jac
	var pointJac bls12381.G1Jac
	pointJac.FromAffine(point)

	for exponent.Sign() > 0 {
		if exponent.Bit(0) == 1 {
			result.AddAssign(&pointJac)
		}
		pointJac.DoubleAssign()
		exponent.Rsh(exponent, 1)
	}

	//var res bls12381.G1Affine
	//res.FromJacobian(&result)
	//return &res
	return &result
}
