package kzg

import (
	"crypto/sha256"
	"fmt"
	"sync"

	bls12381 "github.com/consensys/gnark-crypto/ecc/bls12-381"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/crate-crypto/go-eth-kzg/internal/utils"
)

func OriBatchOpen(commitments []bls12381.G1Affine, p []Polynomial, z []fr.Element, ck *CommitKey, numGoRoutines int) (BatchOpeningProof, error) {
	if len(p) == 0 || len(p) > len(ck.G1) {
		return BatchOpeningProof{}, ErrInvalidPolynomialSize
	}

	// Add before calling OriBatchOpen or at the start of OriBatchOpen
	if len(commitments) != len(p) || len(p) != len(z) {
		panic(fmt.Sprintf("Input slices must have the same length: commitments=%d, p=%d, z=%d", len(commitments), len(p), len(z)))
	}
	for i := range p {
		if len(p[i]) != len(p[0]) {
			panic(fmt.Sprintf("All polynomials must have the same length: p[%d]=%d, p[0]=%d", i, len(p[i]), len(p[0])))
		}
	}

	//y[i] = f_i(z_i)
	y := make([]fr.Element, len(z))

	for i := range p {
		y[i] = eval(p[i], z[i])
	}

	// ∑_{i=1}^k q_i(x)
	//q := make([]fr.Element, len(z))
	// With this:
	q := make([]fr.Element, len(p[0]))

	// q_i(x)
	q_ := make([][]fr.Element, len(z))
	for i := range q_ {
		q_[i] = make([]fr.Element, len(p[i]))
	}

	// q_i(x) = (f_i(x) - f_i(z_i)) / (x - z_i)
	for i := range p {
		q_[i] = dividePolyByXminusA(p[i], y[i], z[i])

		//assume same degree
		for j := range q_[i] {
			q[j].Add(&q[j], &q_[i][j])
		}
	}

	//r=H({C_i},{z_i},{f_i(z_i)})
	var buf []byte

	for _, C_i := range commitments {
		buf = append(buf, C_i.Marshal()...)
	}

	for _, z_i := range z {
		buf = append(buf, z_i.Marshal()...)
	}

	for _, y_i := range y {
		buf = append(buf, y_i.Marshal()...)
	}

	h := sha256.New()
	h.Write(buf)

	digest := h.Sum(nil)
	var r fr.Element
	r.SetBytes(digest[:])

	// Compute r_i
	rPowers := utils.ComputePowers(r, uint(len(commitments)))

	// assuming all polys same degree, pad if needed
	riqi := make([]fr.Element, len(p[0]))

	for i := range q_ {
		for j := range q_[i] {
			tmp := new(fr.Element).Mul(&q_[i][j], &rPowers[i])
			riqi[j].Add(&riqi[j], tmp)
		}
	}

	//W = G^{∑_{i=1}^k r_i*q_i(x)}
	W, err := Commit(riqi, ck, numGoRoutines)
	if err != nil {
		return BatchOpeningProof{}, err
	}

	//t=H(r,W)
	h1 := sha256.New()
	h1.Write(r.Marshal()[:])
	h1.Write(W.Marshal()[:])

	digest1 := h1.Sum(nil)
	var t fr.Element
	t.SetBytes(digest1[:])

	//q = make([]fr.Element, len(q_))
	q = make([]fr.Element, len(p[0]))

	// ∑_{i=1}^k r_i*q_i(x)/(t-z_i)
	for i := range q_ {
		var temp fr.Element
		temp.Sub(&t, &z[i])
		temp.Inverse(&temp)

		for j := range q_[i] {
			//temp.Mul(&q_[i][j], &temp)
			// q[j].Add(&q[j], new(fr.Element).Mul(&q_[i][j], &temp2))
			temp2 := new(fr.Element).Mul(&q_[i][j], &rPowers[i])
			temp2.Mul(temp2, &temp)
			q[j].Add(&q[j], temp2)

		}
	}

	//X = G^{∑_{i=1}^k r_i*q_i(x)/(t-z_i)}
	X, err := Commit(q, ck, numGoRoutines)
	if err != nil {
		return BatchOpeningProof{}, err
	}

	res := BatchOpeningProof{
		InputPoint:   z,
		ClaimedValue: y,
	}

	res.QuotientCommitmentW.Set(W)
	res.QuotientCommitmentX.Set(X)

	return res, nil
}

func LagrangeOriBatchOpen(domain *Domain, commitments []bls12381.G1Affine, p []Polynomial, z []fr.Element, ck *CommitKey, numGoRoutines int) (BatchOpeningProof, error) {
	if len(p) == 0 || len(p) > len(ck.G1) {
		return BatchOpeningProof{}, ErrInvalidPolynomialSize
	}

	//y[i] = f_i(z_i)
	y := make([]fr.Element, len(z))
	// ∑_{i=1}^k q_i(x)
	//q := make([]fr.Element, len(z))
	// With this:
	q := make([]fr.Element, len(p[0]))

	// q_i(x)
	q_ := make([]Polynomial, len(z))

	for i := range p {
		tmp, indexInDomain, err := domain.evaluateLagrangePolynomial(p[i], z[i])
		if err != nil {
			return BatchOpeningProof{}, err
		}
		y[i] = *tmp

		temp, erro := domain.computeQuotientPoly(p[i], indexInDomain, y[i], z[i])
		if erro != nil {
			return BatchOpeningProof{}, erro
		}
		q_[i] = temp

		//assume same degree
		for j := range q_[i] {
			q[j].Add(&q[j], &q_[i][j])
		}
	}

	//r=H({C_i},{z_i},{f_i(z_i)})
	var buf []byte

	for _, C_i := range commitments {
		buf = append(buf, C_i.Marshal()...)
	}

	for _, z_i := range z {
		buf = append(buf, z_i.Marshal()...)
	}

	for _, y_i := range y {
		buf = append(buf, y_i.Marshal()...)
	}

	h := sha256.New()
	h.Write(buf)

	digest := h.Sum(nil)
	var r fr.Element
	r.SetBytes(digest[:])

	// Compute r_i
	rPowers := utils.ComputePowers(r, uint(len(commitments)))

	// assuming all polys same degree, pad if needed
	riqi := make([]fr.Element, len(p[0]))

	for i := range q_ {
		for j := range q_[i] {
			tmp := new(fr.Element).Mul(&q_[i][j], &rPowers[i])
			riqi[j].Add(&riqi[j], tmp)
		}
	}

	//W = G^{∑_{i=1}^k r_i*q_i(x)}
	W, err := Commit(riqi, ck, numGoRoutines)
	if err != nil {
		return BatchOpeningProof{}, err
	}

	//t=H(r,W)
	h1 := sha256.New()
	h1.Write(r.Marshal()[:])
	h1.Write(W.Marshal()[:])

	digest1 := h1.Sum(nil)
	var t fr.Element
	t.SetBytes(digest1[:])

	//q = make([]fr.Element, len(q_))
	q = make([]fr.Element, len(p[0]))

	// ∑_{i=1}^k r_i*q_i(x)/(t-z_i)
	for i := range q_ {
		var temp fr.Element
		temp.Sub(&t, &z[i])
		temp.Inverse(&temp)

		for j := range q_[i] {
			//temp.Mul(&q_[i][j], &temp)
			// q[j].Add(&q[j], new(fr.Element).Mul(&q_[i][j], &temp2))
			temp2 := new(fr.Element).Mul(&q_[i][j], &rPowers[i])
			temp2.Mul(temp2, &temp)
			q[j].Add(&q[j], temp2)

		}
	}

	//X = G^{∑_{i=1}^k r_i*q_i(x)/(t-z_i)}
	X, err := Commit(q, ck, numGoRoutines)
	if err != nil {
		return BatchOpeningProof{}, err
	}

	res := BatchOpeningProof{
		InputPoint:   z,
		ClaimedValue: y,
	}

	res.QuotientCommitmentW.Set(W)
	res.QuotientCommitmentX.Set(X)

	return res, nil
}

func OptimisedLagrangeOriBatchOpen(domain *Domain, commitments []bls12381.G1Affine, p []Polynomial, z []fr.Element, ck *CommitKey, numGoRoutines int) (BatchOpeningProof, error) {
	if len(p) == 0 || len(p) > len(ck.G1) {
		return BatchOpeningProof{}, ErrInvalidPolynomialSize
	}

	//y[i] = f_i(z_i)
	y := make([]fr.Element, len(z))
	// ∑_{i=1}^k q_i(x)
	//q := make([]fr.Element, len(z))
	// With this:
	q := make([]fr.Element, len(p[0]))

	// q_i(x)
	q_ := make([]Polynomial, len(z))

	var wg sync.WaitGroup
	for i := range p {
    	wg.Add(1)
    	go func(i int) {
        	defer wg.Done()
        	tmp, indexInDomain, err := domain.evaluateLagrangePolynomial(p[i], z[i])
        	if err != nil { /* handle error, e.g. send to channel */ return }
        	y[i] = *tmp

        	temp, erro := domain.computeQuotientPoly(p[i], indexInDomain, y[i], z[i])
        	if erro != nil { /* handle error */ return }
        	q_[i] = temp
    	}(i)
	}
	wg.Wait()

	// Then sum q_[i] into q as before
	for i := range q_ {
    	for j := range q_[i] {
        	q[j].Add(&q[j], &q_[i][j])
    	}
	}

	//r=H({C_i},{z_i},{f_i(z_i)})
	var buf []byte

	for _, C_i := range commitments {
		buf = append(buf, C_i.Marshal()...)
	}

	for _, z_i := range z {
		buf = append(buf, z_i.Marshal()...)
	}

	for _, y_i := range y {
		buf = append(buf, y_i.Marshal()...)
	}

	h := sha256.New()
	h.Write(buf)

	digest := h.Sum(nil)
	var r fr.Element
	r.SetBytes(digest[:])

	// Compute r_i
	rPowers := utils.ComputePowers(r, uint(len(commitments)))

	// assuming all polys same degree, pad if needed
	riqi := make([]fr.Element, len(p[0]))

	for i := range q_ {
		for j := range q_[i] {
			tmp := new(fr.Element).Mul(&q_[i][j], &rPowers[i])
			riqi[j].Add(&riqi[j], tmp)
		}
	}

	//W = G^{∑_{i=1}^k r_i*q_i(x)}
	W, err := Commit(riqi, ck, numGoRoutines)
	if err != nil {
		return BatchOpeningProof{}, err
	}

	//t=H(r,W)
	h1 := sha256.New()
	h1.Write(r.Marshal()[:])
	h1.Write(W.Marshal()[:])

	digest1 := h1.Sum(nil)
	var t fr.Element
	t.SetBytes(digest1[:])

	//q = make([]fr.Element, len(q_))
	q = make([]fr.Element, len(p[0]))

	// ∑_{i=1}^k r_i*q_i(x)/(t-z_i)
	for i := range q_ {
		var temp fr.Element
		temp.Sub(&t, &z[i])
		temp.Inverse(&temp)

		for j := range q_[i] {
			//temp.Mul(&q_[i][j], &temp)
			// q[j].Add(&q[j], new(fr.Element).Mul(&q_[i][j], &temp2))
			temp2 := new(fr.Element).Mul(&q_[i][j], &rPowers[i])
			temp2.Mul(temp2, &temp)
			q[j].Add(&q[j], temp2)

		}
	}

	//X = G^{∑_{i=1}^k r_i*q_i(x)/(t-z_i)}
	X, err := Commit(q, ck, numGoRoutines)
	if err != nil {
		return BatchOpeningProof{}, err
	}

	res := BatchOpeningProof{
		InputPoint:   z,
		ClaimedValue: y,
	}

	res.QuotientCommitmentW.Set(W)
	res.QuotientCommitmentX.Set(X)

	return res, nil
}

// Single user batch opening using Monomial basis
func BatchOpen(commitments []bls12381.G1Affine, p []Polynomial, z []fr.Element, ck *CommitKey, numGoRoutines int) (BatchOpeningProof, error) {
	if len(p) == 0 || len(p) > len(ck.G1) {
		return BatchOpeningProof{}, ErrInvalidPolynomialSize
	}

	//y[i] = f_i(z_i)
	y := make([]fr.Element, len(z))

	for i := range p {
		y[i] = eval(p[i], z[i])
	}

	// ∑_{i=1}^k q_i(x)
	//q := make([]fr.Element, len(z))
	// With this:
	q := make([]fr.Element, len(p[0]))

	// q_i(x)
	q_ := make([][]fr.Element, len(z))
	for i := range q_ {
		q_[i] = make([]fr.Element, len(p[i]))
	}

	// q_i(x) = (f_i(x) - f_i(z_i)) / (x - z_i)
	for i := range p {
		q_[i] = dividePolyByXminusA(p[i], y[i], z[i])

		//assume same degree
		for j := range q_[i] {
			q[j].Add(&q[j], &q_[i][j])
		}
	}

	//W = G^{∑_{i=1}^k q_i(x)}
	W, err := Commit(q, ck, numGoRoutines)
	if err != nil {
		return BatchOpeningProof{}, err
	}

	//t=H({C_i},{z_i},{f_i(z_i)},W)
	var buf []byte

	for _, C_i := range commitments {
		buf = append(buf, C_i.Marshal()...)
	}

	for _, z_i := range z {
		buf = append(buf, z_i.Marshal()...)
	}

	for _, y_i := range y {
		buf = append(buf, y_i.Marshal()...)
	}

	h := sha256.New()
	h.Write(buf)
	h.Write(W.Marshal()[:])

	digest := h.Sum(nil)
	var t fr.Element
	t.SetBytes(digest[:])

	//q = make([]fr.Element, len(q_))
	q = make([]fr.Element, len(p[0]))

	// ∑_{i=1}^k q_i(x)/(t-z_i)
	for i := range q_ {
		var temp fr.Element
		temp.Sub(&t, &z[i])
		temp.Inverse(&temp)

		for j := range q_[i] {
			//temp.Mul(&q_[i][j], &temp)
			q[j].Add(&q[j], new(fr.Element).Mul(&q_[i][j], &temp))
		}
	}

	//X = G^{∑_{i=1}^k q_i(x)/(t-z_i)}
	X, err := Commit(q, ck, numGoRoutines)
	if err != nil {
		return BatchOpeningProof{}, err
	}

	res := BatchOpeningProof{
		InputPoint:   z,
		ClaimedValue: y,
	}

	res.QuotientCommitmentW.Set(W)
	res.QuotientCommitmentX.Set(X)

	return res, nil
}

// eval returns p(point) where p is interpreted as a polynomial
// ∑_{i<len(p)}p[i]Xⁱ
// https://github.com/Consensys/gnark-crypto/blob/56600883e0e9f9b159e9c7000b94e76185ec3d0d/ecc/bls12-381/kzg/kzg.go#L55
func eval(p []fr.Element, point fr.Element) fr.Element {
	var res fr.Element
	n := len(p)
	res.Set(&p[n-1])
	for i := n - 2; i >= 0; i-- {
		res.Mul(&res, &point).Add(&res, &p[i])
	}
	return res
}

// dividePolyByXminusA computes (f-f(a))/(x-a), in canonical basis, in regular form
// edited from:
// https://github.com/Consensys/gnark-crypto/blob/56600883e0e9f9b159e9c7000b94e76185ec3d0d/ecc/bls12-381/kzg/kzg.go#L566
func dividePolyByXminusA(f []fr.Element, fa, a fr.Element) []fr.Element {
	q := make([]fr.Element, len(f))
	copy(q, f)

	// first we compute f-f(a)
	q[0].Sub(&q[0], &fa)

	// now we use synthetic division to divide by x-a
	var t fr.Element
	for i := len(q) - 2; i >= 0; i-- {
		t.Mul(&q[i+1], &a)

		q[i].Add(&q[i], &t)
	}

	// the result is of degree deg(f)-1
	return q[1:]
}

// Single user batch opening using Lagrange basis
func LagrangeBatchOpen(domain *Domain, commitments []bls12381.G1Affine, p []Polynomial, z []fr.Element, ck *CommitKey, numGoRoutines int) (BatchOpeningProof, error) {
	if len(p) == 0 || len(p) > len(ck.G1) {
		return BatchOpeningProof{}, ErrInvalidPolynomialSize
	}

	//y[i] = f_i(z_i)
	y := make([]fr.Element, len(z))
	// ∑_{i=1}^k q_i(x)
	//q := make([]fr.Element, len(z))
	// With this:
	q := make([]fr.Element, len(p[0]))

	// q_i(x)
	q_ := make([]Polynomial, len(z))

	for i := range p {
		tmp, indexInDomain, err := domain.evaluateLagrangePolynomial(p[i], z[i])
		if err != nil {
			return BatchOpeningProof{}, err
		}
		y[i] = *tmp

		temp, erro := domain.computeQuotientPoly(p[i], indexInDomain, y[i], z[i])
		if erro != nil {
			return BatchOpeningProof{}, erro
		}
		q_[i] = temp

		//assume same degree
		for j := range q_[i] {
			q[j].Add(&q[j], &q_[i][j])
		}
	}

	//W = G^{∑_{i=1}^k q_i(x)}
	W, err := Commit(q, ck, numGoRoutines)
	if err != nil {
		return BatchOpeningProof{}, err
	}

	//t=H({C_i},{z_i},{f_i(z_i)},W)
	var buf []byte

	for _, C_i := range commitments {
		buf = append(buf, C_i.Marshal()...)
	}

	for _, z_i := range z {
		buf = append(buf, z_i.Marshal()...)
	}

	for _, y_i := range y {
		buf = append(buf, y_i.Marshal()...)
	}

	h := sha256.New()
	h.Write(buf)
	h.Write(W.Marshal()[:])

	digest := h.Sum(nil)
	var t fr.Element
	t.SetBytes(digest[:])

	//q = make([]fr.Element, len(q_))
	q = make([]fr.Element, len(p[0]))

	// ∑_{i=1}^k q_i(x)/(t-z_i)
	for i := range q_ {
		var temp fr.Element
		temp.Sub(&t, &z[i])
		temp.Inverse(&temp)

		for j := range q_[i] {
			q[j].Add(&q[j], new(fr.Element).Mul(&q_[i][j], &temp))
		}
	}

	//X = G^{∑_{i=1}^k q_i(x)/(t-z_i)}
	X, err := Commit(q, ck, numGoRoutines)
	if err != nil {
		return BatchOpeningProof{}, err
	}

	res := BatchOpeningProof{
		InputPoint:   z,
		ClaimedValue: y,
	}

	res.QuotientCommitmentW.Set(W)
	res.QuotientCommitmentX.Set(X)

	return res, nil
}

// Open verifies that a polynomial f(x) when evaluated at a point `z` is equal to `f(z)`
//
// numGoRoutines is used to configure the amount of concurrency needed. Setting this
// value to a negative number or 0 will make it default to the number of CPUs.
//
// [compute_kzg_proof_impl]: https://github.com/ethereum/consensus-specs/blob/017a8495f7671f5fff2075a9bfc9238c1a0982f8/specs/deneb/polynomial-commitments.md#compute_kzg_proof_impl
func Open(domain *Domain, p Polynomial, evaluationPoint fr.Element, ck *CommitKey, numGoRoutines int) (OpeningProof, error) {
	if len(p) == 0 || len(p) > len(ck.G1) {
		return OpeningProof{}, ErrInvalidPolynomialSize
	}

	outputPoint, indexInDomain, err := domain.evaluateLagrangePolynomial(p, evaluationPoint)
	if err != nil {
		return OpeningProof{}, err
	}

	// Compute the quotient polynomial
	quotientPoly, err := domain.computeQuotientPoly(p, indexInDomain, *outputPoint, evaluationPoint)
	if err != nil {
		return OpeningProof{}, err
	}

	// Commit to Quotient polynomial
	quotientCommit, err := Commit(quotientPoly, ck, numGoRoutines)
	if err != nil {
		return OpeningProof{}, err
	}

	res := OpeningProof{
		InputPoint:   evaluationPoint,
		ClaimedValue: *outputPoint,
	}

	res.QuotientCommitment.Set(quotientCommit)

	return res, nil
}

// computeQuotientPoly computes q(X) = (f(X) - f(z)) / (X - z) in Lagrange form.
//
// We refer to the result q(X) as the quotient polynomial.
//
// The division needs to be handled differently if `z` is an element in the domain
// because the naive formula would compute 0/0. Hence, you will observe that this function
// will follow a different code-path depending on this condition.
//
// In our situation, both f(z) and whether z is inside the domain are always known to the caller,
// so we just take is as input rather than (re-)computing it ourself. The method does not check that those
// values provided are correct.
//
// indexInDomain needs to be set to -1 to indicate that z is not in the domain and to the index in the domain if it is.
//
// The matching code for this method is in `compute_kzg_proof_impl` where the quotient polynomial
// is computed.
func (domain *Domain) computeQuotientPoly(f Polynomial, indexInDomain int64, fz, z fr.Element) (Polynomial, error) {
	if domain.Cardinality != uint64(len(f)) {
		return nil, ErrPolynomialMismatchedSizeDomain
	}

	if indexInDomain != -1 {
		// Note: the uint64 conversion is both semantically correct and safer
		// than accepting an `int``, since we know it shouldn't be negative
		// and it should cause a panic, if not checked; uint64(-1) = 2^64 -1
		return domain.computeQuotientPolyOnDomain(f, uint64(indexInDomain))
	}

	return domain.computeQuotientPolyOutsideDomain(f, fz, z)
}

// computeQuotientPolyOutsideDomain computes q(X) = (f(X) - f(z)) / (X - z) in lagrange form where `z` is not in the domain.
//
// This is the implementation of computeQuotientPoly for the case where z is not in the domain.
// Since both input and output polynomials are given in evaluation form, this method just performs the desired operation pointwise.
func (domain *Domain) computeQuotientPolyOutsideDomain(f Polynomial, fz, z fr.Element) (Polynomial, error) {
	// Compute the lagrange form of the denominator X - z.
	// This means that we need to compute w - z for all points w in the domain.
	tmpDenom := make(Polynomial, len(f))
	for i := 0; i < len(f); i++ {
		tmpDenom[i].Sub(&domain.Roots[i], &z)
	}

	// To invert the denominator polynomial at each point of the domain, we perform a batch-inversion.
	// Since `z` is not in the domain, we are sure that there are no zeroes in this inversion.
	//
	// Note: if there was a zero, the gnark-crypto library would skip
	// it and not panic.
	// Note: the returned slice is a new slice, thus we are free to use tmpDenom.
	denominator := fr.BatchInvert(tmpDenom)

	// Compute the lagrange form of the numerator f(X) - f(z)
	// Since f(X) is already in lagrange form, we can compute f(X) - f(z)
	// by shifting all elements in f(X) by f(z)
	numerator := tmpDenom
	for i := 0; i < len(f); i++ {
		numerator[i].Sub(&f[i], &fz)
	}

	// Compute the quotient q(X)
	for i := 0; i < len(f); i++ {
		denominator[i].Mul(&denominator[i], &numerator[i])
	}

	return denominator, nil
}

// computeQuotientPolyOnDomain computes (f(X) - f(z)) / (X - z) in Lagrange form where `z` is in the domain.
//
// This is the implementation of computeQuotientPoly for the case where the evaluation point is in the domain.
//
// [compute_quotient_eval_within_domain]: https://github.com/ethereum/consensus-specs/blob/017a8495f7671f5fff2075a9bfc9238c1a0982f8/specs/deneb/polynomial-commitments.md#compute_quotient_eval_within_domain
func (domain *Domain) computeQuotientPolyOnDomain(f Polynomial, index uint64) (Polynomial, error) {
	fz := f[index]
	z := domain.Roots[index]
	invZ := domain.PreComputedInverses[index]

	// Compute the evaluation of X - z at every point in the domain.
	rootsMinusZ := make([]fr.Element, domain.Cardinality)
	for i := 0; i < int(domain.Cardinality); i++ {
		rootsMinusZ[i].Sub(&domain.Roots[i], &z)
	}

	// Since we know that `z` is in the domain, rootsMinusZ[index] will be zero.
	// We set this value to `1` instead to compute the batch inversion without having to special-case here.
	// This way, the value of rootsMinusZ[index] will stay untouched.
	// Note: The underlying gnark-crypto library will not panic if
	// one of the elements is zero, but this is not common across libraries so we just set it to one.
	rootsMinusZ[index].SetOne()

	// Evaluation of 1/(X-z) at every point of the domain, except for index.
	invRootsMinusZ := fr.BatchInvert(rootsMinusZ)

	// The rootsMinusZ is now free to reuse, since BatchInvert returned
	// a fresh slice. But we need to ensure to set the value for 'index' to zero
	quotientPoly := rootsMinusZ
	quotientPoly[index] = fr.Element{}

	for j := 0; j < int(domain.Cardinality); j++ {
		// Check if we are on the current root of unity
		// Note: For notations below, we use `m` to denote `index`
		if uint64(j) == index {
			continue
		}

		// Compute q_j = f_j / w^j - w^m for j != m.
		// This is exactly the same as in the computeQuotientPolyOutsideDomain - case.
		//
		// Note: f_j is the numerator of the quotient polynomial ie f_j = f[j] - f(z)
		//
		//
		var q_j fr.Element
		q_j.Sub(&f[j], &fz)
		q_j.Mul(&q_j, &invRootsMinusZ[j])
		quotientPoly[j] = q_j

		// Compute the contribution to q_m coming from the j'th term of the input.
		// This term is given by
		// q_m_j = (f_j / w^m - w^j) * (w^j/w^m) , where w^m = z
		//		 = - q_j * w^{j-m}
		//
		// We _could_ find 1 / w^{j-m} via a lookup table
		// but we want to avoid lookup tables because
		// the roots are bit-reversed which can make the
		// code less readable.
		var q_m_j fr.Element
		q_m_j.Neg(&q_j)
		q_m_j.Mul(&q_m_j, &domain.Roots[j])
		q_m_j.Mul(&q_m_j, &invZ)

		quotientPoly[index].Add(&quotientPoly[index], &q_m_j)
	}

	return quotientPoly, nil
}
