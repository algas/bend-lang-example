# mul.bend: 乗算の単調性と、最小・最大の補題。

import Base
import ./nat.bend as N
import ./interval.bend as I
import ./dy.bend as D

# Signs
# -----

# 0 <= z
def ZNN(z: I.Z) -> Data:
  match z:
    case I.Z{p, n}:
      N.LE(n, p)

# z <= 0
def ZNP(z: I.Z) -> Data:
  match z:
    case I.Z{p, n}:
      N.LE(p, n)

def DNN(x: I.Dy) -> Data:
  match x:
    case I.Dy{z, k}:
      ZNN(z)

def DNP(x: I.Dy) -> Data:
  match x:
    case I.Dy{z, k}:
      ZNP(z)

def dsign(x: I.Dy) -> DNN(x) | DNP(x):
  match x:
    case I.Dy{I.Z{p, n}, k}:
      N.le_total(n, p)

# Integer products
# ----------------

# a (δ + wn, wn) と δ a は同じ値（Nat の等式）
def nn_eq(+ap: Nat, +an: Nat, +d: Nat, +wn: Nat)
  -> {Nat.add(Nat.add(Nat.mul(wn, an), Nat.mul(Nat.add(d, wn), ap)), Nat.mul(d, an)) == Nat.add(Nat.mul(d, ap), Nat.add(Nat.mul(wn, ap), Nat.mul(Nat.add(d, wn), an))) : Nat}:
  %N.mul_dist_r(d, wn, ap) : {Nat.add(Nat.add(Nat.mul(wn, an), _), Nat.mul(d, an)) == Nat.add(Nat.mul(d, ap), Nat.add(Nat.mul(wn, ap), Nat.mul(Nat.add(d, wn), an))) : Nat}
  %N.mul_dist_r(d, wn, an) : {Nat.add(Nat.add(Nat.mul(wn, an), Nat.add(Nat.mul(d, ap), Nat.mul(wn, ap))), Nat.mul(d, an)) == Nat.add(Nat.mul(d, ap), Nat.add(Nat.mul(wn, ap), _)) : Nat}
  N.four(Nat.mul(wn, an), Nat.mul(d, ap), Nat.mul(wn, ap), Nat.mul(d, an))

# 0 <= w ならば a w == (wp - wn) a（両向きの不等式で表す）
def zmul_nn1(a: I.Z, +wp: Nat, +wn: Nat, +h: N.LE(wn, wp)) -> D.ZLE(I.Z.mul(a, I.Z{wp, wn}), I.Z.smul(Nat.sub(wp, wn), a)):
  match a:
    case I.Z{+ap, +an}:
      +d = Nat.sub(wp, wn)
      %N.sub_add(wp, wn, h) : D.ZLE(I.Z.mul(I.Z{ap, an}, I.Z{_, wn}), I.Z.smul(d, I.Z{ap, an}))
      N.le_of_eq(
        Nat.add(Nat.add(Nat.mul(wn, an), Nat.mul(Nat.add(d, wn), ap)), Nat.mul(d, an)),
        Nat.add(Nat.mul(d, ap), Nat.add(Nat.mul(wn, ap), Nat.mul(Nat.add(d, wn), an))),
        nn_eq(ap, an, d, wn))

def zmul_nn2(a: I.Z, +wp: Nat, +wn: Nat, +h: N.LE(wn, wp)) -> D.ZLE(I.Z.smul(Nat.sub(wp, wn), a), I.Z.mul(a, I.Z{wp, wn})):
  match a:
    case I.Z{+ap, +an}:
      +d = Nat.sub(wp, wn)
      %N.sub_add(wp, wn, h) : D.ZLE(I.Z.smul(d, I.Z{ap, an}), I.Z.mul(I.Z{ap, an}, I.Z{_, wn}))
      N.le_of_eq(
        Nat.add(Nat.mul(d, ap), Nat.add(Nat.mul(wn, ap), Nat.mul(Nat.add(d, wn), an))),
        Nat.add(Nat.add(Nat.mul(wn, an), Nat.mul(Nat.add(d, wn), ap)), Nat.mul(d, an)),
        Equal.sym(Nat,
          Nat.add(Nat.add(Nat.mul(wn, an), Nat.mul(Nat.add(d, wn), ap)), Nat.mul(d, an)),
          Nat.add(Nat.mul(d, ap), Nat.add(Nat.mul(wn, ap), Nat.mul(Nat.add(d, wn), an))),
          nn_eq(ap, an, d, wn)))

# u <= v, 0 <= w ならば u w <= v w
def zmul_mono(+u: I.Z, +v: I.Z, w: I.Z, h: D.ZLE(u, v), nn: ZNN(w)) -> D.ZLE(I.Z.mul(u, w), I.Z.mul(v, w)):
  match w:
    case I.Z{+wp, +wn}:
      +n = nn
      +d = Nat.sub(wp, wn)
      +w2 = {I.Z{wp, wn} : I.Z}
      a = D.zle_trans(I.Z.mul(u, w2), I.Z.smul(d, u), I.Z.smul(d, v), zmul_nn1(u, wp, wn, n), D.zle_smul(d, u, v, h))
      D.zle_trans(I.Z.mul(u, w2), I.Z.smul(d, v), I.Z.mul(v, w2), a, zmul_nn2(v, wp, wn, n))

# a (-w) == -(a w)
def zmul_neg_r(a: I.Z, w: I.Z) -> {I.Z.mul(a, I.Z.neg(w)) == I.Z.neg(I.Z.mul(a, w)) : I.Z}:
  match a w:
    case I.Z{+ap, +an} I.Z{+wp, +wn}:
      D.zeq(
        Nat.add(Nat.mul(wp, an), Nat.mul(wn, ap)), Nat.add(Nat.mul(wp, ap), Nat.mul(wn, an)),
        Nat.add(Nat.mul(wn, ap), Nat.mul(wp, an)), Nat.add(Nat.mul(wn, an), Nat.mul(wp, ap)),
        N.add_comm(Nat.mul(wp, an), Nat.mul(wn, ap)), N.add_comm(Nat.mul(wp, ap), Nat.mul(wn, an)))

# -a <= -b ならば b <= a
def zneg_flip(a: I.Z, b: I.Z, h: D.ZLE(I.Z.neg(a), I.Z.neg(b))) -> D.ZLE(b, a):
  match a b:
    case I.Z{+ap, +an} I.Z{+bp, +bn}:
      N.le_rw(Nat.add(an, bp), Nat.add(bn, ap), Nat.add(bp, an), Nat.add(ap, bn), N.add_comm(an, bp), N.add_comm(bn, ap), h)

# u <= v, w <= 0 ならば v w <= u w
def zmul_mono_np(+u: I.Z, +v: I.Z, w: I.Z, h: D.ZLE(u, v), np: ZNP(w)) -> D.ZLE(I.Z.mul(v, w), I.Z.mul(u, w)):
  match w:
    case I.Z{+wp, +wn}:
      +w2 = {I.Z{wp, wn} : I.Z}
      m = zmul_mono(u, v, I.Z{wn, wp}, h, np)
      r = D.zle_rw(
        I.Z.mul(u, I.Z.neg(w2)), I.Z.mul(v, I.Z.neg(w2)),
        I.Z.neg(I.Z.mul(u, w2)), I.Z.neg(I.Z.mul(v, w2)),
        zmul_neg_r(u, w2), zmul_neg_r(v, w2), m)
      zneg_flip(I.Z.mul(u, w2), I.Z.mul(v, w2), r)

# (m a) b == m (a b)
def zmul_smul_l(+m: Nat, a: I.Z, b: I.Z) -> {I.Z.mul(I.Z.smul(m, a), b) == I.Z.smul(m, I.Z.mul(a, b)) : I.Z}:
  match a b:
    case I.Z{+ap, +an} I.Z{+bp, +bn}:
      D.zeq(
        Nat.add(Nat.mul(bn, Nat.mul(m, an)), Nat.mul(bp, Nat.mul(m, ap))), Nat.add(Nat.mul(bn, Nat.mul(m, ap)), Nat.mul(bp, Nat.mul(m, an))),
        Nat.mul(m, Nat.add(Nat.mul(bn, an), Nat.mul(bp, ap))), Nat.mul(m, Nat.add(Nat.mul(bn, ap), Nat.mul(bp, an))),
        N.mul_pull(m, bn, an, bp, ap), N.mul_pull(m, bn, ap, bp, an))

# m (k a) == (k m) a
def zsmul_smul(+m: Nat, +k: Nat, a: I.Z) -> {I.Z.smul(m, I.Z.smul(k, a)) == I.Z.smul(Nat.mul(k, m), a) : I.Z}:
  match a:
    case I.Z{+p, +n}:
      D.zeq(
        Nat.mul(m, Nat.mul(k, p)), Nat.mul(m, Nat.mul(k, n)),
        Nat.mul(Nat.mul(k, m), p), Nat.mul(Nat.mul(k, m), n),
        N.mul_swap_assoc(m, k, p), N.mul_swap_assoc(m, k, n))

# a b == b a
def zmul_comm(a: I.Z, b: I.Z) -> {I.Z.mul(a, b) == I.Z.mul(b, a) : I.Z}:
  match a b:
    case I.Z{+ap, +an} I.Z{+bp, +bn}:
      D.zeq(
        Nat.add(Nat.mul(bn, an), Nat.mul(bp, ap)), Nat.add(Nat.mul(bn, ap), Nat.mul(bp, an)),
        Nat.add(Nat.mul(an, bn), Nat.mul(ap, bp)), Nat.add(Nat.mul(an, bp), Nat.mul(ap, bn)),
        N.comm2(bn, an, bp, ap), N.comm2x(bn, ap, bp, an))

# Dyadic products
# ---------------

# a <= x, 0 <= y ならば a y <= x y
def dle_mul_r(a: I.Dy, x: I.Dy, y: I.Dy, h: D.DLE(a, x), nn: DNN(y)) -> D.DLE(I.Dy.mul(a, y), I.Dy.mul(x, y)):
  match a x y:
    case I.Dy{+za, +ka} I.Dy{+zx, +kx} I.Dy{+zy, +ky}:
      +pa = I.pow2(ka)
      +px = I.pow2(kx)
      +py = I.pow2(ky)
      m1 = zmul_mono(I.Z.smul(px, za), I.Z.smul(pa, zx), zy, h, nn)
      m2 = D.zle_smul(py, I.Z.mul(I.Z.smul(px, za), zy), I.Z.mul(I.Z.smul(pa, zx), zy), m1)
      %D.pow2_add_r(kx, ky) : D.ZLE(I.Z.smul(_, I.Z.mul(za, zy)), I.Z.smul(I.pow2(Nat.add(ka, ky)), I.Z.mul(zx, zy)))
      %D.pow2_add_r(ka, ky) : D.ZLE(I.Z.smul(Nat.mul(px, py), I.Z.mul(za, zy)), I.Z.smul(_, I.Z.mul(zx, zy)))
      %zsmul_smul(py, px, I.Z.mul(za, zy)) : D.ZLE(_, I.Z.smul(Nat.mul(pa, py), I.Z.mul(zx, zy)))
      %zsmul_smul(py, pa, I.Z.mul(zx, zy)) : D.ZLE(I.Z.smul(py, I.Z.smul(px, I.Z.mul(za, zy))), _)
      %zmul_smul_l(px, za, zy) : D.ZLE(I.Z.smul(py, _), I.Z.smul(py, I.Z.smul(pa, I.Z.mul(zx, zy))))
      %zmul_smul_l(pa, zx, zy) : D.ZLE(I.Z.smul(py, I.Z.mul(I.Z.smul(px, za), zy)), I.Z.smul(py, _))
      m2

# a <= x, y <= 0 ならば x y <= a y
def dle_mul_r_np(a: I.Dy, x: I.Dy, y: I.Dy, h: D.DLE(a, x), np: DNP(y)) -> D.DLE(I.Dy.mul(x, y), I.Dy.mul(a, y)):
  match a x y:
    case I.Dy{+za, +ka} I.Dy{+zx, +kx} I.Dy{+zy, +ky}:
      +pa = I.pow2(ka)
      +px = I.pow2(kx)
      +py = I.pow2(ky)
      m1 = zmul_mono_np(I.Z.smul(px, za), I.Z.smul(pa, zx), zy, h, np)
      m2 = D.zle_smul(py, I.Z.mul(I.Z.smul(pa, zx), zy), I.Z.mul(I.Z.smul(px, za), zy), m1)
      %D.pow2_add_r(ka, ky) : D.ZLE(I.Z.smul(_, I.Z.mul(zx, zy)), I.Z.smul(I.pow2(Nat.add(kx, ky)), I.Z.mul(za, zy)))
      %D.pow2_add_r(kx, ky) : D.ZLE(I.Z.smul(Nat.mul(pa, py), I.Z.mul(zx, zy)), I.Z.smul(_, I.Z.mul(za, zy)))
      %zsmul_smul(py, pa, I.Z.mul(zx, zy)) : D.ZLE(_, I.Z.smul(Nat.mul(px, py), I.Z.mul(za, zy)))
      %zsmul_smul(py, px, I.Z.mul(za, zy)) : D.ZLE(I.Z.smul(py, I.Z.smul(pa, I.Z.mul(zx, zy))), _)
      %zmul_smul_l(pa, zx, zy) : D.ZLE(I.Z.smul(py, _), I.Z.smul(py, I.Z.smul(px, I.Z.mul(za, zy))))
      %zmul_smul_l(px, za, zy) : D.ZLE(I.Z.smul(py, I.Z.mul(I.Z.smul(pa, zx), zy)), I.Z.smul(py, _))
      m2

# x y <= y x（値として等しい）
def dmul_comm(x: I.Dy, y: I.Dy) -> D.DLE(I.Dy.mul(x, y), I.Dy.mul(y, x)):
  match x y:
    case I.Dy{+zx, +kx} I.Dy{+zy, +ky}:
      %N.add_comm(kx, ky) : D.ZLE(I.Z.smul(I.pow2(_), I.Z.mul(zx, zy)), I.Z.smul(I.pow2(Nat.add(kx, ky)), I.Z.mul(zy, zx)))
      %zmul_comm(zx, zy) : D.ZLE(I.Z.smul(I.pow2(Nat.add(kx, ky)), I.Z.mul(zx, zy)), I.Z.smul(I.pow2(Nat.add(kx, ky)), _))
      D.zle_refl(I.Z.smul(I.pow2(Nat.add(kx, ky)), I.Z.mul(zx, zy)))

# c <= y, 0 <= a ならば a c <= a y
def dle_mul_l(+c: I.Dy, +y: I.Dy, +a: I.Dy, h: D.DLE(c, y), nn: DNN(a)) -> D.DLE(I.Dy.mul(a, c), I.Dy.mul(a, y)):
  D.dle_trans(I.Dy.mul(a, c), I.Dy.mul(c, a), I.Dy.mul(a, y), dmul_comm(a, c),
    D.dle_trans(I.Dy.mul(c, a), I.Dy.mul(y, a), I.Dy.mul(a, y), dle_mul_r(c, y, a, h, nn), dmul_comm(y, a)))

# c <= y, a <= 0 ならば a y <= a c
def dle_mul_l_np(+c: I.Dy, +y: I.Dy, +a: I.Dy, h: D.DLE(c, y), np: DNP(a)) -> D.DLE(I.Dy.mul(a, y), I.Dy.mul(a, c)):
  D.dle_trans(I.Dy.mul(a, y), I.Dy.mul(y, a), I.Dy.mul(a, c), dmul_comm(a, y),
    D.dle_trans(I.Dy.mul(y, a), I.Dy.mul(c, a), I.Dy.mul(a, c), dle_mul_r_np(c, y, a, h, np), dmul_comm(c, a)))

# Min and max
# -----------

def minl_go(x: I.Dy, y: I.Dy, b: Bool, e: {b == I.Dy.le(x, y) : Bool}) -> D.DLE(I.Dy.pick(b, x, y), x):
  match x y b:
    case I.Dy{I.Z{+px, +nx}, +kx} I.Dy{I.Z{+py, +ny}, +ky} True{}:
      +a = I.pow2(kx)
      +c = I.pow2(ky)
      +l = Nat.add(Nat.mul(c, px), Nat.mul(a, ny))
      +r = Nat.add(Nat.mul(a, py), Nat.mul(c, nx))
      D.dle_refl(I.Dy{I.Z{px, nx}, kx})
    case I.Dy{I.Z{+px, +nx}, +kx} I.Dy{I.Z{+py, +ny}, +ky} False{}:
      +a = I.pow2(kx)
      +c = I.pow2(ky)
      +l = Nat.add(Nat.mul(c, px), Nat.mul(a, ny))
      +r = Nat.add(Nat.mul(a, py), Nat.mul(c, nx))
      N.le_of_not_is_le(l, r, Equal.sym(Bool, False{}, Nat.is_le(l, r), e))

def minr_go(x: I.Dy, y: I.Dy, b: Bool, e: {b == I.Dy.le(x, y) : Bool}) -> D.DLE(I.Dy.pick(b, x, y), y):
  match x y b:
    case I.Dy{I.Z{+px, +nx}, +kx} I.Dy{I.Z{+py, +ny}, +ky} True{}:
      +a = I.pow2(kx)
      +c = I.pow2(ky)
      +l = Nat.add(Nat.mul(c, px), Nat.mul(a, ny))
      +r = Nat.add(Nat.mul(a, py), Nat.mul(c, nx))
      N.le_of_is_le(l, r, Equal.sym(Bool, True{}, Nat.is_le(l, r), e))
    case I.Dy{I.Z{+px, +nx}, +kx} I.Dy{I.Z{+py, +ny}, +ky} False{}:
      +a = I.pow2(kx)
      +c = I.pow2(ky)
      +l = Nat.add(Nat.mul(c, px), Nat.mul(a, ny))
      +r = Nat.add(Nat.mul(a, py), Nat.mul(c, nx))
      D.dle_refl(I.Dy{I.Z{py, ny}, ky})

def maxl_go(x: I.Dy, y: I.Dy, b: Bool, e: {b == I.Dy.le(x, y) : Bool}) -> D.DLE(x, I.Dy.pick(b, y, x)):
  match x y b:
    case I.Dy{I.Z{+px, +nx}, +kx} I.Dy{I.Z{+py, +ny}, +ky} True{}:
      +a = I.pow2(kx)
      +c = I.pow2(ky)
      +l = Nat.add(Nat.mul(c, px), Nat.mul(a, ny))
      +r = Nat.add(Nat.mul(a, py), Nat.mul(c, nx))
      N.le_of_is_le(l, r, Equal.sym(Bool, True{}, Nat.is_le(l, r), e))
    case I.Dy{I.Z{+px, +nx}, +kx} I.Dy{I.Z{+py, +ny}, +ky} False{}:
      +a = I.pow2(kx)
      +c = I.pow2(ky)
      +l = Nat.add(Nat.mul(c, px), Nat.mul(a, ny))
      +r = Nat.add(Nat.mul(a, py), Nat.mul(c, nx))
      D.dle_refl(I.Dy{I.Z{px, nx}, kx})

def maxr_go(x: I.Dy, y: I.Dy, b: Bool, e: {b == I.Dy.le(x, y) : Bool}) -> D.DLE(y, I.Dy.pick(b, y, x)):
  match x y b:
    case I.Dy{I.Z{+px, +nx}, +kx} I.Dy{I.Z{+py, +ny}, +ky} True{}:
      +a = I.pow2(kx)
      +c = I.pow2(ky)
      +l = Nat.add(Nat.mul(c, px), Nat.mul(a, ny))
      +r = Nat.add(Nat.mul(a, py), Nat.mul(c, nx))
      D.dle_refl(I.Dy{I.Z{py, ny}, ky})
    case I.Dy{I.Z{+px, +nx}, +kx} I.Dy{I.Z{+py, +ny}, +ky} False{}:
      +a = I.pow2(kx)
      +c = I.pow2(ky)
      +l = Nat.add(Nat.mul(c, px), Nat.mul(a, ny))
      +r = Nat.add(Nat.mul(a, py), Nat.mul(c, nx))
      N.le_of_not_is_le(l, r, Equal.sym(Bool, False{}, Nat.is_le(l, r), e))

def min_le_l(+x: I.Dy, +y: I.Dy) -> D.DLE(I.Dy.min(x, y), x):
  minl_go(x, y, I.Dy.le(x, y), {==})

def min_le_r(+x: I.Dy, +y: I.Dy) -> D.DLE(I.Dy.min(x, y), y):
  minr_go(x, y, I.Dy.le(x, y), {==})

def le_max_l(+x: I.Dy, +y: I.Dy) -> D.DLE(x, I.Dy.max(x, y)):
  maxl_go(x, y, I.Dy.le(x, y), {==})

def le_max_r(+x: I.Dy, +y: I.Dy) -> D.DLE(y, I.Dy.max(x, y)):
  maxr_go(x, y, I.Dy.le(x, y), {==})

def min_mono_go(+m1: I.Dy, +m2: I.Dy, +u: I.Dy, +v: I.Dy, h1: D.DLE(m1, u), h2: D.DLE(m2, v), b: Bool) -> D.DLE(I.Dy.min(m1, m2), I.Dy.pick(b, u, v)):
  match b:
    case True{}:
      D.dle_trans(I.Dy.min(m1, m2), m1, u, min_le_l(m1, m2), h1)
    case False{}:
      D.dle_trans(I.Dy.min(m1, m2), m2, v, min_le_r(m1, m2), h2)

# m1 <= u, m2 <= v ならば min(m1, m2) <= min(u, v)
def min_mono(+m1: I.Dy, +m2: I.Dy, +u: I.Dy, +v: I.Dy, h1: D.DLE(m1, u), h2: D.DLE(m2, v)) -> D.DLE(I.Dy.min(m1, m2), I.Dy.min(u, v)):
  min_mono_go(m1, m2, u, v, h1, h2, I.Dy.le(u, v))

def max_mono_go(+u: I.Dy, +v: I.Dy, +m1: I.Dy, +m2: I.Dy, h1: D.DLE(u, m1), h2: D.DLE(v, m2), b: Bool) -> D.DLE(I.Dy.pick(b, v, u), I.Dy.max(m1, m2)):
  match b:
    case True{}:
      D.dle_trans(v, m2, I.Dy.max(m1, m2), h2, le_max_r(m1, m2))
    case False{}:
      D.dle_trans(u, m1, I.Dy.max(m1, m2), h1, le_max_l(m1, m2))

# u <= m1, v <= m2 ならば max(u, v) <= max(m1, m2)
def max_mono(+u: I.Dy, +v: I.Dy, +m1: I.Dy, +m2: I.Dy, h1: D.DLE(u, m1), h2: D.DLE(v, m2)) -> D.DLE(I.Dy.max(u, v), I.Dy.max(m1, m2)):
  max_mono_go(u, v, m1, m2, h1, h2, I.Dy.le(u, v))

# Brackets
# --------

def bracket_go(+a: I.Dy, +c: I.Dy, +y: I.Dy, +d: I.Dy, hc: D.DLE(c, y), hd: D.DLE(y, d), s: DNN(a) | DNP(a))
  -> D.DLE(I.Dy.min(I.Dy.mul(a, c), I.Dy.mul(a, d)), I.Dy.mul(a, y)) & D.DLE(I.Dy.mul(a, y), I.Dy.max(I.Dy.mul(a, c), I.Dy.mul(a, d))):
  match s:
    case Inl{+nn}:
      +ac = I.Dy.mul(a, c)
      +ad = I.Dy.mul(a, d)
      +ay = I.Dy.mul(a, y)
      (D.dle_trans(I.Dy.min(ac, ad), ac, ay, min_le_l(ac, ad), dle_mul_l(c, y, a, hc, nn)),
       D.dle_trans(ay, ad, I.Dy.max(ac, ad), dle_mul_l(y, d, a, hd, nn), le_max_r(ac, ad)))
    case Inr{+np}:
      +ac = I.Dy.mul(a, c)
      +ad = I.Dy.mul(a, d)
      +ay = I.Dy.mul(a, y)
      (D.dle_trans(I.Dy.min(ac, ad), ad, ay, min_le_r(ac, ad), dle_mul_l_np(y, d, a, hd, np)),
       D.dle_trans(ay, ac, I.Dy.max(ac, ad), dle_mul_l_np(c, y, a, hc, np), le_max_l(ac, ad)))

# c <= y <= d ならば a y は [min(a c, a d), max(a c, a d)] に入る
def bracket(+a: I.Dy, +c: I.Dy, +y: I.Dy, +d: I.Dy, hc: D.DLE(c, y), hd: D.DLE(y, d))
  -> D.DLE(I.Dy.min(I.Dy.mul(a, c), I.Dy.mul(a, d)), I.Dy.mul(a, y)) & D.DLE(I.Dy.mul(a, y), I.Dy.max(I.Dy.mul(a, c), I.Dy.mul(a, d))):
  bracket_go(a, c, y, d, hc, hd, dsign(a))

def bracket_r_go(+a: I.Dy, +x: I.Dy, +b: I.Dy, +y: I.Dy, ha: D.DLE(a, x), hb: D.DLE(x, b), s: DNN(y) | DNP(y))
  -> D.DLE(I.Dy.min(I.Dy.mul(a, y), I.Dy.mul(b, y)), I.Dy.mul(x, y)) & D.DLE(I.Dy.mul(x, y), I.Dy.max(I.Dy.mul(a, y), I.Dy.mul(b, y))):
  match s:
    case Inl{+nn}:
      +ay = I.Dy.mul(a, y)
      +by = I.Dy.mul(b, y)
      +xy = I.Dy.mul(x, y)
      (D.dle_trans(I.Dy.min(ay, by), ay, xy, min_le_l(ay, by), dle_mul_r(a, x, y, ha, nn)),
       D.dle_trans(xy, by, I.Dy.max(ay, by), dle_mul_r(x, b, y, hb, nn), le_max_r(ay, by)))
    case Inr{+np}:
      +ay = I.Dy.mul(a, y)
      +by = I.Dy.mul(b, y)
      +xy = I.Dy.mul(x, y)
      (D.dle_trans(I.Dy.min(ay, by), by, xy, min_le_r(ay, by), dle_mul_r_np(x, b, y, hb, np)),
       D.dle_trans(xy, ay, I.Dy.max(ay, by), dle_mul_r_np(a, x, y, ha, np), le_max_l(ay, by)))

# a <= x <= b ならば x y は [min(a y, b y), max(a y, b y)] に入る
def bracket_r(+a: I.Dy, +x: I.Dy, +b: I.Dy, +y: I.Dy, ha: D.DLE(a, x), hb: D.DLE(x, b))
  -> D.DLE(I.Dy.min(I.Dy.mul(a, y), I.Dy.mul(b, y)), I.Dy.mul(x, y)) & D.DLE(I.Dy.mul(x, y), I.Dy.max(I.Dy.mul(a, y), I.Dy.mul(b, y))):
  bracket_r_go(a, x, b, y, ha, hb, dsign(y))

# Enclosure of a product
# ----------------------

# 3つの挟み込みから、x y が 4つの端点積の [min, max] に入ることを導く
def enclose(+alo: I.Dy, +ahi: I.Dy, +blo: I.Dy, +bhi: I.Dy, +x: I.Dy, +y: I.Dy,
  b1: D.DLE(I.Dy.min(I.Dy.mul(alo, blo), I.Dy.mul(alo, bhi)), I.Dy.mul(alo, y)) & D.DLE(I.Dy.mul(alo, y), I.Dy.max(I.Dy.mul(alo, blo), I.Dy.mul(alo, bhi))),
  b2: D.DLE(I.Dy.min(I.Dy.mul(ahi, blo), I.Dy.mul(ahi, bhi)), I.Dy.mul(ahi, y)) & D.DLE(I.Dy.mul(ahi, y), I.Dy.max(I.Dy.mul(ahi, blo), I.Dy.mul(ahi, bhi))),
  b3: D.DLE(I.Dy.min(I.Dy.mul(alo, y), I.Dy.mul(ahi, y)), I.Dy.mul(x, y)) & D.DLE(I.Dy.mul(x, y), I.Dy.max(I.Dy.mul(alo, y), I.Dy.mul(ahi, y))))
  -> D.DLE(I.Dy.min(I.Dy.min(I.Dy.mul(alo, blo), I.Dy.mul(alo, bhi)), I.Dy.min(I.Dy.mul(ahi, blo), I.Dy.mul(ahi, bhi))), I.Dy.mul(x, y))
   & D.DLE(I.Dy.mul(x, y), I.Dy.max(I.Dy.max(I.Dy.mul(alo, blo), I.Dy.mul(alo, bhi)), I.Dy.max(I.Dy.mul(ahi, blo), I.Dy.mul(ahi, bhi)))):
  (l1, u1) = b1
  (l2, u2) = b2
  (l3, u3) = b3
  +p1 = I.Dy.mul(alo, blo)
  +p2 = I.Dy.mul(alo, bhi)
  +p3 = I.Dy.mul(ahi, blo)
  +p4 = I.Dy.mul(ahi, bhi)
  +ay = I.Dy.mul(alo, y)
  +by = I.Dy.mul(ahi, y)
  +xy = I.Dy.mul(x, y)
  (D.dle_trans(I.Dy.min(I.Dy.min(p1, p2), I.Dy.min(p3, p4)), I.Dy.min(ay, by), xy, min_mono(I.Dy.min(p1, p2), I.Dy.min(p3, p4), ay, by, l1, l2), l3),
   D.dle_trans(xy, I.Dy.max(ay, by), I.Dy.max(I.Dy.max(p1, p2), I.Dy.max(p3, p4)), u3, max_mono(ay, by, I.Dy.max(p1, p2), I.Dy.max(p3, p4), u1, u2)))
