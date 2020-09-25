package sm2

import (
	"crypto/elliptic"
	"math/big"
)

type Secp256k1Curve struct {
	*elliptic.CurveParams
	A *big.Int
}

var secp256k1 *Secp256k1Curve

func initSecp256k1() {
	secp256k1 = &Secp256k1Curve{CurveParams: &elliptic.CurveParams{Name: "secp256k1"}}
	secp256k1.P, _ = new(big.Int).SetString("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16)
	secp256k1.N, _ = new(big.Int).SetString("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16)
	secp256k1.A = new(big.Int)
	secp256k1.B = new(big.Int).SetInt64(7)
	secp256k1.Gx, _ = new(big.Int).SetString("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798", 16)
	secp256k1.Gy, _ = new(big.Int).SetString("483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8", 16)
	secp256k1.BitSize = 256
}

// Secp256k1 returns a Curve which implements secp256k1 (see SEC 2, section 2.4.1)
//
// The cryptographic operations do not use constant-time algorithms.
func Secp256k1() elliptic.Curve {
	initonce.Do(initAll)
	return secp256k1
}

// Params returns the elliptic CurveParams of the implemented curve.
func (curve *Secp256k1Curve) Params() *elliptic.CurveParams {
	return curve.CurveParams
}

// IsOnCurve returns whether or not a (x, y) point is on the curve.
func (curve *Secp256k1Curve) IsOnCurve(x, y *big.Int) bool {
	// y² = x³ + ax + b
	y2 := new(big.Int).Mul(y, y)
	y2.Mod(y2, curve.P)

	x3 := new(big.Int).Mul(x, x)
	x3.Mul(x3, x)

	aX := new(big.Int).Mul(curve.A, x)
	aX.Mod(aX, curve.P)

	x3.Add(x3, aX)
	x3.Add(x3, curve.B)
	x3.Mod(x3, curve.P)

	return x3.Cmp(y2) == 0
}

// affineFromJacobian reverses the Jacobian transform. See the comment at the
// top of the file. If the point is ∞ it returns 0, 0.
func (curve *Secp256k1Curve) affineFromJacobian(x, y, z *big.Int) (xOut, yOut *big.Int) {
	if z.Sign() == 0 {
		return new(big.Int), new(big.Int)
	}

	zinv := new(big.Int).ModInverse(z, curve.P)
	zinvsq := new(big.Int).Mul(zinv, zinv)

	xOut = new(big.Int).Mul(x, zinvsq)
	xOut.Mod(xOut, curve.P)
	zinvsq.Mul(zinvsq, zinv)
	yOut = new(big.Int).Mul(y, zinvsq)
	yOut.Mod(yOut, curve.P)
	return
}

// Add returns the sum of two affine points.
func (curve *Secp256k1Curve) Add(x1, y1, x2, y2 *big.Int) (*big.Int, *big.Int) {
	z1 := zForAffine(x1, y1)
	z2 := zForAffine(x2, y2)
	return curve.affineFromJacobian(curve.addJacobian(x1, y1, z1, x2, y2, z2))
}

// addJacobian takes two points in Jacobian coordinates, (x1, y1, z1) and
// (x2, y2, z2) and returns their sum, also in Jacobian form.
func (curve *Secp256k1Curve) addJacobian(x1, y1, z1, x2, y2, z2 *big.Int) (*big.Int, *big.Int, *big.Int) {
	// See http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-add-2007-bl
	x3, y3, z3 := new(big.Int), new(big.Int), new(big.Int)
	if z1.Sign() == 0 {
		x3.Set(x2)
		y3.Set(y2)
		z3.Set(z2)
		return x3, y3, z3
	}
	if z2.Sign() == 0 {
		x3.Set(x1)
		y3.Set(y1)
		z3.Set(z1)
		return x3, y3, z3
	}

	z1z1 := new(big.Int).Mul(z1, z1)
	z1z1.Mod(z1z1, curve.P)
	z2z2 := new(big.Int).Mul(z2, z2)
	z2z2.Mod(z2z2, curve.P)

	u1 := new(big.Int).Mul(x1, z2z2)
	u1.Mod(u1, curve.P)
	u2 := new(big.Int).Mul(x2, z1z1)
	u2.Mod(u2, curve.P)
	h := new(big.Int).Sub(u2, u1)
	xEqual := h.Sign() == 0
	if h.Sign() == -1 {
		h.Add(h, curve.P)
	}
	i := new(big.Int).Lsh(h, 1)
	i.Mul(i, i)
	j := new(big.Int).Mul(h, i)

	s1 := new(big.Int).Mul(y1, z2)
	s1.Mul(s1, z2z2)
	s1.Mod(s1, curve.P)
	s2 := new(big.Int).Mul(y2, z1)
	s2.Mul(s2, z1z1)
	s2.Mod(s2, curve.P)
	r := new(big.Int).Sub(s2, s1)
	if r.Sign() == -1 {
		r.Add(r, curve.P)
	}
	yEqual := r.Sign() == 0
	if xEqual && yEqual {
		return curve.doubleJacobian(x1, y1, z1)
	}
	r.Lsh(r, 1)
	v := new(big.Int).Mul(u1, i)

	x3.Set(r)
	x3.Mul(x3, x3)
	x3.Sub(x3, j)
	x3.Sub(x3, v)
	x3.Sub(x3, v)
	x3.Mod(x3, curve.P)

	y3.Set(r)
	v.Sub(v, x3)
	y3.Mul(y3, v)
	s1.Mul(s1, j)
	s1.Lsh(s1, 1)
	y3.Sub(y3, s1)
	y3.Mod(y3, curve.P)

	z3.Add(z1, z2)
	z3.Mul(z3, z3)
	z3.Sub(z3, z1z1)
	z3.Sub(z3, z2z2)
	z3.Mul(z3, h)
	z3.Mod(z3, curve.P)

	return x3, y3, z3
}

// doubleJacobian takes a point in Jacobian coordinates, (x, y, z), and
// returns its double, also in Jacobian form.
func (curve *Secp256k1Curve) doubleJacobian(x, y, z *big.Int) (*big.Int, *big.Int, *big.Int) {
	// See http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#doubling-dbl-2007-bl
	xx := new(big.Int).Mul(x, x)
	xx.Mod(xx, curve.P)

	yy := new(big.Int).Mul(y, y)
	yy.Mod(yy, curve.P)

	yyyy := new(big.Int).Mul(yy, yy)
	yyyy.Mod(yyyy, curve.P)

	zz := new(big.Int).Mul(z, z)
	zz.Mod(zz, curve.P)

	s := new(big.Int).Add(x, yy)
	s.Mul(s, s)
	s.Sub(s, xx)
	if s.Sign() == -1 {
		s.Add(s, curve.P)
	}
	s.Sub(s, yyyy)
	if s.Sign() == -1 {
		s.Add(s, curve.P)
	}
	s.Lsh(s, 1)
	s.Mod(s, curve.P)

	m := new(big.Int).Lsh(xx, 1)
	m.Add(m, xx)
	m2 := new(big.Int).Mul(zz, zz)
	m2.Mul(curve.A, m2)
	m.Add(m, m2)
	m.Mod(m, curve.P)

	t := new(big.Int).Mul(m, m)
	t2 := new(big.Int).Lsh(s, 1)
	t.Sub(t, t2)
	if t.Sign() == -1 {
		t.Add(t, curve.P)
	}
	t.Mod(t, curve.P)

	x3 := new(big.Int).Set(t)

	y3 := new(big.Int).Sub(s, t)
	if y3.Sign() == -1 {
		y3.Add(y3, curve.P)
	}
	y3.Mul(y3, m)
	yyyy8 := new(big.Int).Lsh(yyyy, 3)
	y3.Sub(y3, yyyy8)
	if y3.Sign() == -1 {
		y3.Add(y3, curve.P)
	}
	y3.Mod(y3, curve.P)

	z3 := new(big.Int).Add(y, z)
	z3.Mul(z3, z3)
	z3.Sub(z3, yy)
	if z3.Sign() == -1 {
		z3.Add(z3, curve.P)
	}
	z3.Sub(z3, zz)
	if z3.Sign() == -1 {
		z3.Add(z3, curve.P)
	}
	z3.Mod(z3, curve.P)

	return x3, y3, z3
}

// ScalarMult multiplies the point (Bx, By) by the scalar k using repeated doubling.
func (curve *Secp256k1Curve) ScalarMult(Bx, By *big.Int, k []byte) (*big.Int, *big.Int) {
	Bz := new(big.Int).SetInt64(1)
	x, y, z := new(big.Int), new(big.Int), new(big.Int)

	for _, byte := range k {
		for bitNum := 0; bitNum < 8; bitNum++ {
			x, y, z = curve.doubleJacobian(x, y, z)
			if byte&0x80 == 0x80 {
				x, y, z = curve.addJacobian(Bx, By, Bz, x, y, z)
			}
			byte <<= 1
		}
	}

	return curve.affineFromJacobian(x, y, z)
}

// ScalarBaseMult multiplies the base point by the scalar k using repeated doubling.
func (curve *Secp256k1Curve) ScalarBaseMult(k []byte) (*big.Int, *big.Int) {
	return curve.ScalarMult(curve.Gx, curve.Gy, k)
}

