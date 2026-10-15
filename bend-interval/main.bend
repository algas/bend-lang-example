# main.bend: 区間演算の実行例。
#
#   bend main.bend
#
# 端点は (p - n) / 2^k の二進有理数。各演算の結果は分母 2^10 へ外向きに
# 丸める。包含性の証明は PROOF.bend にある。

import Base
import ./interval.bend as I

def one() -> I.Iv:
  I.iv(I.dy(1n, 0n, 0n), I.dy(1n, 0n, 0n))

# x(1 - x) を区間で素朴に評価
def logistic(+x: I.Iv, +t: Nat) -> I.Iv:
  I.Iv.mul(x, I.Iv.sub(one(), x, t), t)

def basics(+x: I.Iv, +y: I.Iv, +t: Nat) -> String:
  "x + y = " ++ I.Iv.show(I.Iv.add(x, y, t)) ++ "\n" ++
  "x - y = " ++ I.Iv.show(I.Iv.sub(x, y, t)) ++ "\n" ++
  "x * y = " ++ I.Iv.show(I.Iv.mul(x, y, t))

def thirds(+th: I.Iv, +t: Nat) -> String:
  three = I.iv(I.dy(3n, 0n, 0n), I.dy(3n, 0n, 0n))
  "3 * th = " ++ I.Iv.show(I.Iv.mul(three, th, t)) ++ "\n" ++
  "th * th = " ++ I.Iv.show(I.Iv.mul(th, th, t))

def main() -> IO(Unit):
  do IO<Unit>:
    # x ∈ [1, 1.5], y ∈ [-0.25, 0.25]
    IO.print(basics(I.iv(I.dy(1n, 0n, 0n), I.dy(3n, 0n, 1n)), I.iv(I.dy(0n, 1n, 2n), I.dy(1n, 0n, 2n)), 10n))
    # th = [341/1024, 342/1024] は 1/3 を含む
    IO.print(thirds(I.iv(I.dy(341n, 0n, 10n), I.dy(342n, 0n, 10n)), 10n))
    # 依存性問題: x(1-x) の真の値域は [0.1875, 0.25] だが、区間演算は広めに囲む
    IO.print("x(1-x), x in [0.25, 0.5] = " ++ I.Iv.show(logistic(I.iv(I.dy(1n, 0n, 2n), I.dy(1n, 0n, 1n)), 10n)))
