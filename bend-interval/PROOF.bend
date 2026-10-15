# PROOF.bend: LAWS.bend の証明。補題は nat.bend（自然数）、dy.bend
# （整数・二進有理数）、mul.bend（乗算と最小・最大）にある。
#
#   bend PROOF.bend             # 全 law を検査
#   bend PROOF.bend --verdict   # Lean で証明済みのカーネルで再検査

import Base
import ./interval.bend as I
import ./dy.bend as D
import ./mul.bend as M
import ./LAWS.bend as Laws

def Laws.round_down(x, t):
  D.dle_down(x, t)

def Laws.round_up(x, t):
  D.dle_up(x, t)

def Laws.add_incl(x, y, a, b, t, hx, hy):
  match a b:
    case I.Iv{+alo, +ahi} I.Iv{+blo, +bhi}:
      (hx1, hx2) = hx
      (hy1, hy2) = hy
      +lo = I.Dy.add(alo, blo)
      +hi = I.Dy.add(ahi, bhi)
      +s = I.Dy.add(x, y)
      (
        D.dle_trans(I.Dy.down(lo, t), lo, s, D.dle_down(lo, t), D.dle_add(alo, x, blo, y, hx1, hy1)),
        D.dle_trans(s, hi, I.Dy.up(hi, t), D.dle_add(x, ahi, y, bhi, hx2, hy2), D.dle_up(hi, t))
      )

def Laws.neg_incl(x, a, hx):
  match a:
    case I.Iv{+lo, +hi}:
      (h1, h2) = hx
      (D.dle_neg(x, hi, h2), D.dle_neg(lo, x, h1))

def Laws.sub_incl(x, y, a, b, t, hx, hy):
  Laws.add_incl(x, I.Dy.neg(y), a, I.Iv.neg(b), t, hx, Laws.neg_incl(y, b, hy))

def mul_incl_go(+x: I.Dy, +y: I.Dy, +lo: I.Dy, +hi: I.Dy, +t: Nat, e: D.DLE(lo, I.Dy.mul(x, y)) & D.DLE(I.Dy.mul(x, y), hi))
  -> D.DLE(I.Dy.down(lo, t), I.Dy.mul(x, y)) & D.DLE(I.Dy.mul(x, y), I.Dy.up(hi, t)):
  (l, u) = e
  +xy = I.Dy.mul(x, y)
  (D.dle_trans(I.Dy.down(lo, t), lo, xy, D.dle_down(lo, t), l),
   D.dle_trans(xy, hi, I.Dy.up(hi, t), u, D.dle_up(hi, t)))

def Laws.mul_incl(x, y, a, b, t, hx, hy):
  match a b:
    case I.Iv{+alo, +ahi} I.Iv{+blo, +bhi}:
      (hx1, hx2) = hx
      (hy1_, hy2_) = hy
      +hy1 = hy1_
      +hy2 = hy2_
      +p1 = I.Dy.mul(alo, blo)
      +p2 = I.Dy.mul(alo, bhi)
      +p3 = I.Dy.mul(ahi, blo)
      +p4 = I.Dy.mul(ahi, bhi)
      e = M.enclose(alo, ahi, blo, bhi, x, y,
        M.bracket(alo, blo, y, bhi, hy1, hy2),
        M.bracket(ahi, blo, y, bhi, hy1, hy2),
        M.bracket_r(alo, x, ahi, y, hx1, hx2))
      mul_incl_go(x, y, I.Dy.min(I.Dy.min(p1, p2), I.Dy.min(p3, p4)), I.Dy.max(I.Dy.max(p1, p2), I.Dy.max(p3, p4)), t, e)
