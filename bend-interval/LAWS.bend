# LAWS.bend: 二進有理数による区間演算の「包含性」。
#
# 人間が書く仕様。x が区間 a に入り、y が区間 b に入るなら、正確な x + y は
# 外向きに丸めた区間 a + b に必ず入る（減算・符号反転も同様）。
# 証明は PROOF.bend にあり、`bend PROOF.bend` がすべてを検査する。

import Base
import ./interval.bend as I
import ./dy.bend as D

# x ∈ [lo, hi]
def In(x: I.Dy, a: I.Iv) -> Type:
  match a:
    case I.Iv{lo, hi}:
      D.DLE(lo, x) & D.DLE(x, hi)

# LAW: 下向き丸めは値を超えない
law round_down:
  for +x: I.Dy
  for +t: Nat
  D.DLE(I.Dy.down(x, t), x)

# LAW: 上向き丸めは値を下回らない
law round_up:
  for +x: I.Dy
  for +t: Nat
  D.DLE(x, I.Dy.up(x, t))

# LAW: 加算の包含性（丸め先の精度 t は任意）
law add_incl:
  for +x: I.Dy
  for +y: I.Dy
  for a: I.Iv
  for b: I.Iv
  for +t: Nat
  for hx: In(x, a)
  for hy: In(y, b)
  In(I.Dy.add(x, y), I.Iv.add(a, b, t))

# LAW: 符号反転の包含性
law neg_incl:
  for +x: I.Dy
  for a: I.Iv
  for hx: In(x, a)
  In(I.Dy.neg(x), I.Iv.neg(a))

# LAW: 減算の包含性
law sub_incl:
  for +x: I.Dy
  for +y: I.Dy
  for +a: I.Iv
  for +b: I.Iv
  for +t: Nat
  for hx: In(x, a)
  for hy: In(y, b)
  In(I.Dy.sub(x, y), I.Iv.sub(a, b, t))

# LAW: 乗算の包含性（端点の符号は任意）
law mul_incl:
  for +x: I.Dy
  for +y: I.Dy
  for a: I.Iv
  for b: I.Iv
  for +t: Nat
  for hx: In(x, a)
  for hy: In(y, b)
  In(I.Dy.mul(x, y), I.Iv.mul(a, b, t))
