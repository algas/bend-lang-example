# dy.bend: 整数・二進有理数の順序と、その補題。
# 区間演算の「包含性」の証明は、ここの補題を組み合わせるだけになる。

import Base
import ./nat.bend as N
import ./interval.bend as I

# Order on signed integers
# ------------------------

# (ap - an) <= (bp - bn)  <=>  ap + bn <= bp + an
def ZLE(a: I.Z, b: I.Z) -> Data:
  match a b:
    case I.Z{ap, an} I.Z{bp, bn}:
      N.LE(Nat.add(ap, bn), Nat.add(bp, an))

def zle_refl(a: I.Z) -> ZLE(a, a):
  match a:
    case I.Z{+p, +n}:
      N.le_refl(Nat.add(p, n))

def zle_rw(-a: I.Z, -b: I.Z, -c: I.Z, -d: I.Z, ea: {a == c : I.Z}, eb: {b == d : I.Z}, e: ZLE(a, b)) -> ZLE(c, d):
  %ea : ZLE(_, d)
  %eb : ZLE(a, _)
  e

def zle_trans(a: I.Z, b: I.Z, c: I.Z, ab: ZLE(a, b), bc: ZLE(b, c)) -> ZLE(a, c):
  match a b c:
    case I.Z{+ap, +an} I.Z{+bp, +bn} I.Z{+cp, +cn}:
      s = N.add_mono(Nat.add(ap, bn), Nat.add(bp, an), Nat.add(bp, cn), Nat.add(cp, bn), ab, bc)
      r = N.le_rw(
        Nat.add(Nat.add(ap, bn), Nat.add(bp, cn)), Nat.add(Nat.add(bp, an), Nat.add(cp, bn)),
        Nat.add(Nat.add(ap, cn), Nat.add(bp, bn)), Nat.add(Nat.add(cp, an), Nat.add(bp, bn)),
        N.add4_x(ap, bn, bp, cn), N.add4_y(bp, an, cp, bn), s)
      N.add_cancel_r(Nat.add(bp, bn), Nat.add(ap, cn), Nat.add(cp, an), r)

# a <= b, c <= d ならば a + c <= b + d
def zle_add(a: I.Z, b: I.Z, c: I.Z, d: I.Z, ab: ZLE(a, b), cd: ZLE(c, d)) -> ZLE(I.Z.add(a, c), I.Z.add(b, d)):
  match a b c d:
    case I.Z{+ap, +an} I.Z{+bp, +bn} I.Z{+cp, +cn} I.Z{+dp, +dn}:
      s = N.add_mono(Nat.add(ap, bn), Nat.add(bp, an), Nat.add(cp, dn), Nat.add(dp, cn), ab, cd)
      N.le_rw(
        Nat.add(Nat.add(ap, bn), Nat.add(cp, dn)), Nat.add(Nat.add(bp, an), Nat.add(dp, cn)),
        Nat.add(Nat.add(ap, cp), Nat.add(bn, dn)), Nat.add(Nat.add(bp, dp), Nat.add(an, cn)),
        N.add4_m(ap, bn, cp, dn), N.add4_m(bp, an, dp, cn), s)

# a <= b ならば m a <= m b
def zle_smul(+m: Nat, a: I.Z, b: I.Z, ab: ZLE(a, b)) -> ZLE(I.Z.smul(m, a), I.Z.smul(m, b)):
  match a b:
    case I.Z{+ap, +an} I.Z{+bp, +bn}:
      s = N.mul_mono_l(m, Nat.add(ap, bn), Nat.add(bp, an), ab)
      N.le_rw(
        Nat.mul(m, Nat.add(ap, bn)), Nat.mul(m, Nat.add(bp, an)),
        Nat.add(Nat.mul(m, ap), Nat.mul(m, bn)), Nat.add(Nat.mul(m, bp), Nat.mul(m, an)),
        N.mul_dist_l(m, ap, bn), N.mul_dist_l(m, bp, an), s)

# 1 <= m, m a <= m b ならば a <= b
def zle_cancel(+m: Nat, pos: N.LE(1n, m), a: I.Z, b: I.Z, e: ZLE(I.Z.smul(m, a), I.Z.smul(m, b))) -> ZLE(a, b):
  match a b:
    case I.Z{+ap, +an} I.Z{+bp, +bn}:
      s = N.le_rw(
        Nat.add(Nat.mul(m, ap), Nat.mul(m, bn)), Nat.add(Nat.mul(m, bp), Nat.mul(m, an)),
        Nat.mul(m, Nat.add(ap, bn)), Nat.mul(m, Nat.add(bp, an)),
        N.mul_dist_l_r(m, ap, bn), N.mul_dist_l_r(m, bp, an), e)
      N.mul_cancel_pos(m, pos, Nat.add(ap, bn), Nat.add(bp, an), s)

# Equalities of signed integers
# -----------------------------

def zeq(-a: Nat, -b: Nat, -c: Nat, -d: Nat, ac: {a == c : Nat}, bd: {b == d : Nat}) -> {I.Z{a, b} == I.Z{c, d} : I.Z}:
  %ac : {I.Z{a, b} == I.Z{_, d} : I.Z}
  %bd : {I.Z{a, b} == I.Z{a, _} : I.Z}
  {==}

# m (k a) == k (m a)
def zsmul_comm(+m: Nat, +k: Nat, a: I.Z) -> {I.Z.smul(m, I.Z.smul(k, a)) == I.Z.smul(k, I.Z.smul(m, a)) : I.Z}:
  match a:
    case I.Z{+p, +n}:
      zeq(
        Nat.mul(m, Nat.mul(k, p)), Nat.mul(m, Nat.mul(k, n)),
        Nat.mul(k, Nat.mul(m, p)), Nat.mul(k, Nat.mul(m, n)),
        N.mul_swap(m, k, p), N.mul_swap(m, k, n))

# Powers of two
# -------------

def pow2_pos(k: Nat) -> N.LE(1n, I.pow2(k)):
  match k:
    case 0n:
      Unit{}
    case 1n++j:
      N.le_trans(1n, I.pow2(j), Nat.mul(2n, I.pow2(j)), pow2_pos(j), N.le_add_r(I.pow2(j), Nat.mul(1n, I.pow2(j))))

# Order on dyadic rationals
# -------------------------

# zx / 2^kx <= zy / 2^ky  <=>  2^ky zx <= 2^kx zy
def DLE(x: I.Dy, y: I.Dy) -> Data:
  match x y:
    case I.Dy{zx, kx} I.Dy{zy, ky}:
      ZLE(I.Z.smul(I.pow2(ky), zx), I.Z.smul(I.pow2(kx), zy))

def dle_refl(x: I.Dy) -> DLE(x, x):
  match x:
    case I.Dy{+z, +k}:
      zle_refl(I.Z.smul(I.pow2(k), z))

def dle_trans(x: I.Dy, y: I.Dy, z: I.Dy, xy: DLE(x, y), yz: DLE(y, z)) -> DLE(x, z):
  match x y z:
    case I.Dy{+zx, +kx} I.Dy{+zy, +ky} I.Dy{+zz, +kz}:
      +px = I.pow2(kx)
      +py = I.pow2(ky)
      +pz = I.pow2(kz)
      h1 = zle_smul(pz, I.Z.smul(py, zx), I.Z.smul(px, zy), xy)
      h2 = zle_smul(px, I.Z.smul(pz, zy), I.Z.smul(py, zz), yz)
      h1r = zle_rw(
        I.Z.smul(pz, I.Z.smul(py, zx)), I.Z.smul(pz, I.Z.smul(px, zy)),
        I.Z.smul(pz, I.Z.smul(py, zx)), I.Z.smul(px, I.Z.smul(pz, zy)),
        {==}, zsmul_comm(pz, px, zy), h1)
      h3 = zle_trans(I.Z.smul(pz, I.Z.smul(py, zx)), I.Z.smul(px, I.Z.smul(pz, zy)), I.Z.smul(px, I.Z.smul(py, zz)), h1r, h2)
      h4 = zle_rw(
        I.Z.smul(pz, I.Z.smul(py, zx)), I.Z.smul(px, I.Z.smul(py, zz)),
        I.Z.smul(py, I.Z.smul(pz, zx)), I.Z.smul(py, I.Z.smul(px, zz)),
        zsmul_comm(pz, py, zx), zsmul_comm(px, py, zz), h3)
      zle_cancel(py, pow2_pos(ky), I.Z.smul(pz, zx), I.Z.smul(px, zz), h4)

# 2^(a+b) == 2^a 2^b
def pow2_add(a: Nat, +b: Nat) -> {I.pow2(Nat.add(a, b)) == Nat.mul(I.pow2(a), I.pow2(b)) : Nat}:
  match a:
    case 0n:
      N.add_zero(I.pow2(b))
    case 1n++p:
      %N.mul_assoc_r(2n, I.pow2(p), I.pow2(b)) : {I.pow2(Nat.add(1n+p, b)) == _ : Nat}
      %pow2_add(p, b) : {Nat.mul(2n, I.pow2(Nat.add(p, b))) == Nat.mul(2n, _) : Nat}
      {==}

# 2^a 2^b == 2^(a+b)
def pow2_add_r(+a: Nat, +b: Nat) -> {Nat.mul(I.pow2(a), I.pow2(b)) == I.pow2(Nat.add(a, b)) : Nat}:
  Equal.sym(Nat, I.pow2(Nat.add(a, b)), Nat.mul(I.pow2(a), I.pow2(b)), pow2_add(a, b))

# 加法の単調性で使う並べ替え（Nat 版）:
# b2 (a2 (b1 x)) + a1 (b1 (b2 y)) == (b1 b2) (a2 x + a1 y)
def mono_nat(+a1: Nat, +a2: Nat, +b1: Nat, +b2: Nat, +x: Nat, +y: Nat)
  -> {Nat.add(Nat.mul(b2, Nat.mul(a2, Nat.mul(b1, x))), Nat.mul(a1, Nat.mul(b1, Nat.mul(b2, y)))) == Nat.mul(Nat.mul(b1, b2), Nat.add(Nat.mul(a2, x), Nat.mul(a1, y))) : Nat}:
  +l1 = Nat.mul(b2, Nat.mul(a2, Nat.mul(b1, x)))
  +l2 = Nat.mul(a1, Nat.mul(b1, Nat.mul(b2, y)))
  %N.mul_dist_l_r(Nat.mul(b1, b2), Nat.mul(a2, x), Nat.mul(a1, y)) : {Nat.add(l1, l2) == _ : Nat}
  %N.mul_assoc_r(b1, b2, Nat.mul(a2, x)) : {Nat.add(l1, l2) == Nat.add(_, Nat.mul(Nat.mul(b1, b2), Nat.mul(a1, y))) : Nat}
  %N.mul_assoc_r(b1, b2, Nat.mul(a1, y)) : {Nat.add(l1, l2) == Nat.add(Nat.mul(b1, Nat.mul(b2, Nat.mul(a2, x))), _) : Nat}
  %N.mul_swap(b2, b1, Nat.mul(a2, x)) : {Nat.add(l1, l2) == Nat.add(_, Nat.mul(b1, Nat.mul(b2, Nat.mul(a1, y)))) : Nat}
  %N.mul_swap(a2, b1, x) : {Nat.add(l1, l2) == Nat.add(Nat.mul(b2, _), Nat.mul(b1, Nat.mul(b2, Nat.mul(a1, y)))) : Nat}
  %N.mul_swap(a1, b2, y) : {Nat.add(l1, l2) == Nat.add(l1, Nat.mul(b1, _)) : Nat}
  %N.mul_swap(a1, b1, Nat.mul(b2, y)) : {Nat.add(l1, l2) == Nat.add(l1, _) : Nat}
  {==}

# 同じ並べ替え（整数版）
def mono_z(+a1: Nat, +a2: Nat, +b1: Nat, +b2: Nat, w1: I.Z, w2: I.Z)
  -> {I.Z.add(I.Z.smul(b2, I.Z.smul(a2, I.Z.smul(b1, w1))), I.Z.smul(a1, I.Z.smul(b1, I.Z.smul(b2, w2)))) == I.Z.smul(Nat.mul(b1, b2), I.Z.add(I.Z.smul(a2, w1), I.Z.smul(a1, w2))) : I.Z}:
  match w1 w2:
    case I.Z{+p1, +n1} I.Z{+p2, +n2}:
      zeq(
        Nat.add(Nat.mul(b2, Nat.mul(a2, Nat.mul(b1, p1))), Nat.mul(a1, Nat.mul(b1, Nat.mul(b2, p2)))),
        Nat.add(Nat.mul(b2, Nat.mul(a2, Nat.mul(b1, n1))), Nat.mul(a1, Nat.mul(b1, Nat.mul(b2, n2)))),
        Nat.mul(Nat.mul(b1, b2), Nat.add(Nat.mul(a2, p1), Nat.mul(a1, p2))),
        Nat.mul(Nat.mul(b1, b2), Nat.add(Nat.mul(a2, n1), Nat.mul(a1, n2))),
        mono_nat(a1, a2, b1, b2, p1, p2), mono_nat(a1, a2, b1, b2, n1, n2))

# x1 <= y1, x2 <= y2 ならば x1 + x2 <= y1 + y2（正確な加算の単調性）
def dle_add(x1: I.Dy, y1: I.Dy, x2: I.Dy, y2: I.Dy, h1: DLE(x1, y1), h2: DLE(x2, y2)) -> DLE(I.Dy.add(x1, x2), I.Dy.add(y1, y2)):
  match x1 y1 x2 y2:
    case I.Dy{+z1, +a1} I.Dy{+w1, +b1} I.Dy{+z2, +a2} I.Dy{+w2, +b2}:
      +pa1 = I.pow2(a1)
      +pa2 = I.pow2(a2)
      +pb1 = I.pow2(b1)
      +pb2 = I.pow2(b2)
      +lx = I.Z.add(I.Z.smul(pa2, z1), I.Z.smul(pa1, z2))
      +ly = I.Z.add(I.Z.smul(pb2, w1), I.Z.smul(pb1, w2))
      g1 = zle_smul(pb2, I.Z.smul(pa2, I.Z.smul(pb1, z1)), I.Z.smul(pa2, I.Z.smul(pa1, w1)), zle_smul(pa2, I.Z.smul(pb1, z1), I.Z.smul(pa1, w1), h1))
      g1r = zle_rw(
        I.Z.smul(pb2, I.Z.smul(pa2, I.Z.smul(pb1, z1))), I.Z.smul(pb2, I.Z.smul(pa2, I.Z.smul(pa1, w1))),
        I.Z.smul(pb2, I.Z.smul(pa2, I.Z.smul(pb1, z1))), I.Z.smul(pa2, I.Z.smul(pb2, I.Z.smul(pa1, w1))),
        {==}, zsmul_comm(pb2, pa2, I.Z.smul(pa1, w1)), g1)
      g2 = zle_smul(pa1, I.Z.smul(pb1, I.Z.smul(pb2, z2)), I.Z.smul(pb1, I.Z.smul(pa2, w2)), zle_smul(pb1, I.Z.smul(pb2, z2), I.Z.smul(pa2, w2), h2))
      g2r = zle_rw(
        I.Z.smul(pa1, I.Z.smul(pb1, I.Z.smul(pb2, z2))), I.Z.smul(pa1, I.Z.smul(pb1, I.Z.smul(pa2, w2))),
        I.Z.smul(pa1, I.Z.smul(pb1, I.Z.smul(pb2, z2))), I.Z.smul(pb1, I.Z.smul(pa1, I.Z.smul(pa2, w2))),
        {==}, zsmul_comm(pa1, pb1, I.Z.smul(pa2, w2)), g2)
      g = zle_add(
        I.Z.smul(pb2, I.Z.smul(pa2, I.Z.smul(pb1, z1))), I.Z.smul(pa2, I.Z.smul(pb2, I.Z.smul(pa1, w1))),
        I.Z.smul(pa1, I.Z.smul(pb1, I.Z.smul(pb2, z2))), I.Z.smul(pb1, I.Z.smul(pa1, I.Z.smul(pa2, w2))),
        g1r, g2r)
      %pow2_add_r(b1, b2) : ZLE(I.Z.smul(_, lx), I.Z.smul(I.pow2(Nat.add(a1, a2)), ly))
      %pow2_add_r(a1, a2) : ZLE(I.Z.smul(Nat.mul(pb1, pb2), lx), I.Z.smul(_, ly))
      zle_rw(
        I.Z.add(I.Z.smul(pb2, I.Z.smul(pa2, I.Z.smul(pb1, z1))), I.Z.smul(pa1, I.Z.smul(pb1, I.Z.smul(pb2, z2)))),
        I.Z.add(I.Z.smul(pa2, I.Z.smul(pb2, I.Z.smul(pa1, w1))), I.Z.smul(pb1, I.Z.smul(pa1, I.Z.smul(pa2, w2)))),
        I.Z.smul(Nat.mul(pb1, pb2), lx), I.Z.smul(Nat.mul(pa1, pa2), ly),
        mono_z(pa1, pa2, pb1, pb2, z1, z2), mono_z(pb1, pb2, pa1, pa2, w1, w2), g)

# x <= y ならば -y <= -x
def dle_neg(x: I.Dy, y: I.Dy, h: DLE(x, y)) -> DLE(I.Dy.neg(y), I.Dy.neg(x)):
  match x y:
    case I.Dy{I.Z{+px, +nx}, +kx} I.Dy{I.Z{+py, +ny}, +ky}:
      +a = I.pow2(kx)
      +b = I.pow2(ky)
      N.le_rw(
        Nat.add(Nat.mul(b, px), Nat.mul(a, ny)), Nat.add(Nat.mul(a, py), Nat.mul(b, nx)),
        Nat.add(Nat.mul(a, ny), Nat.mul(b, px)), Nat.add(Nat.mul(b, nx), Nat.mul(a, py)),
        N.add_comm(Nat.mul(b, px), Nat.mul(a, ny)), N.add_comm(Nat.mul(a, py), Nat.mul(b, nx)), h)

# Rounding
# --------

def fl_go(b: Bool, +q: Nat, +a: Nat, +d: Nat, e: {b == Nat.is_le(Nat.mul(d, q), a) : Bool}) -> N.LE(Nat.mul(d, I.fl.pick(b, q)), a):
  match b:
    case True{}:
      N.le_of_is_le(Nat.mul(d, q), a, Equal.sym(Bool, True{}, Nat.is_le(Nat.mul(d, q), a), e))
    case False{}:
      %N.zero_mul_r(d) : N.LE(_, a)
      Unit{}

# d * fl(a, d) <= a
def fl_le(+a: Nat, +d: Nat) -> N.LE(Nat.mul(d, I.fl(a, d)), a):
  fl_go(Nat.is_le(Nat.mul(d, Nat.div(a, d)), a), Nat.div(a, d), a, d, {==})

def cl_go2(b: Bool, +q: Nat, +a: Nat, +d: Nat, pos: N.LE(1n, d), e: {b == Nat.is_le(a, Nat.mul(d, q)) : Bool}) -> N.LE(a, Nat.mul(d, I.cl.pick(b, q, a))):
  match b:
    case True{}:
      N.le_of_is_le(a, Nat.mul(d, q), Equal.sym(Bool, True{}, Nat.is_le(a, Nat.mul(d, q)), e))
    case False{}:
      N.le_mul_pos(a, d, pos)

def cl_go1(b: Bool, +q: Nat, +a: Nat, +d: Nat, pos: N.LE(1n, d), e: {b == Nat.is_le(a, Nat.mul(d, q)) : Bool}) -> N.LE(a, Nat.mul(d, I.cl.pick1(b, q, a, d))):
  match b:
    case True{}:
      N.le_of_is_le(a, Nat.mul(d, q), Equal.sym(Bool, True{}, Nat.is_le(a, Nat.mul(d, q)), e))
    case False{}:
      cl_go2(Nat.is_le(a, Nat.mul(d, 1n+q)), 1n+q, a, d, pos, {==})

# 1 <= d ならば a <= d * cl(a, d)
def cl_ge(+a: Nat, +d: Nat, pos: N.LE(1n, d)) -> N.LE(a, Nat.mul(d, I.cl(a, d))):
  cl_go1(Nat.is_le(a, Nat.mul(d, Nat.div(a, d))), Nat.div(a, d), a, d, pos, {==})

# down(x, t) <= x
def dle_down(x: I.Dy, +t: Nat) -> DLE(I.Dy.down(x, t), x):
  match x:
    case I.Dy{I.Z{+p, +n}, +k}:
      +pt = I.pow2(t)
      +pk = I.pow2(k)
      N.add_mono(
        Nat.mul(pk, I.fl(Nat.mul(pt, p), pk)), Nat.mul(pt, p),
        Nat.mul(pt, n), Nat.mul(pk, I.cl(Nat.mul(pt, n), pk)),
        fl_le(Nat.mul(pt, p), pk), cl_ge(Nat.mul(pt, n), pk, pow2_pos(k)))

# x <= up(x, t)
def dle_up(x: I.Dy, +t: Nat) -> DLE(x, I.Dy.up(x, t)):
  match x:
    case I.Dy{I.Z{+p, +n}, +k}:
      +pt = I.pow2(t)
      +pk = I.pow2(k)
      N.add_mono(
        Nat.mul(pt, p), Nat.mul(pk, I.cl(Nat.mul(pt, p), pk)),
        Nat.mul(pk, I.fl(Nat.mul(pt, n), pk)), Nat.mul(pt, n),
        cl_ge(Nat.mul(pt, p), pk, pow2_pos(k)), fl_le(Nat.mul(pt, n), pk))
