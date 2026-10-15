# interval.bend: 二進有理数による区間演算（外向き丸め）。
#
# 実数の代わりに二進有理数 (p - n) / 2^k を使う。Bend 2 の F32 は公理的で
# 何も証明できないので、浮動小数点は一切使わず、Nat（実行時は u64）だけで
# 計算する。符号付き整数は Nat の対 (p, n) で p - n を表す。
#
#   bun bend2/main.ts main.bend   # 実行例

import Base

# Signed integers
# ---------------

# p - n を表す整数
type Z is Data:
  Z{p: Nat, n: Nat}

def Z.add(a: Z, b: Z) -> Z:
  match a b:
    case Z{ap, an} Z{bp, bn}:
      Z{Nat.add(ap, bp), Nat.add(an, bn)}

def Z.neg(a: Z) -> Z:
  match a:
    case Z{p, n}:
      Z{n, p}

# 自然数倍 m * a
def Z.smul(+m: Nat, a: Z) -> Z:
  match a:
    case Z{p, n}:
      Z{Nat.mul(m, p), Nat.mul(m, n)}

# 積 (ap - an)(bp - bn) = (ap bp + an bn) - (ap bn + an bp)
def Z.mul(a: Z, b: Z) -> Z:
  match a b:
    case Z{+ap, +an} Z{+bp, +bn}:
      Z{Nat.add(Nat.mul(bn, an), Nat.mul(bp, ap)), Nat.add(Nat.mul(bn, ap), Nat.mul(bp, an))}

# Dyadic rationals
# ----------------

# z / 2^k を表す二進有理数
type Dy is Data:
  Dy{z: Z, k: Nat}

def pow2(k: Nat) -> Nat:
  Nat.pow(2n, k)

# 正確な加算（分母 2^kx * 2^ky = 2^(kx+ky) にそろえる。丸めなし）
def Dy.add(x: Dy, y: Dy) -> Dy:
  match x y:
    case Dy{zx, +kx} Dy{zy, +ky}:
      Dy{Z.add(Z.smul(pow2(ky), zx), Z.smul(pow2(kx), zy)), Nat.add(kx, ky)}

def Dy.neg(x: Dy) -> Dy:
  match x:
    case Dy{z, k}:
      Dy{Z.neg(z), k}

def Dy.sub(x: Dy, y: Dy) -> Dy:
  Dy.add(x, Dy.neg(y))

# 正確な乗算（丸めなし）
def Dy.mul(x: Dy, y: Dy) -> Dy:
  match x y:
    case Dy{zx, kx} Dy{zy, ky}:
      Dy{Z.mul(zx, zy), Nat.add(kx, ky)}

# x <= y の判定（実行版）
def Dy.le(x: Dy, y: Dy) -> Bool:
  match x y:
    case Dy{Z{+px, +nx}, +kx} Dy{Z{+py, +ny}, +ky}:
      +a = pow2(kx)
      +b = pow2(ky)
      Nat.is_le(Nat.add(Nat.mul(b, px), Nat.mul(a, ny)), Nat.add(Nat.mul(a, py), Nat.mul(b, nx)))

def Dy.pick(b: Bool, x: Dy, y: Dy) -> Dy:
  match b:
    case True{}:
      x
    case False{}:
      y

def Dy.min(+x: Dy, +y: Dy) -> Dy:
  Dy.pick(Dy.le(x, y), x, y)

def Dy.max(+x: Dy, +y: Dy) -> Dy:
  Dy.pick(Dy.le(x, y), y, x)

# Directed rounding
# -----------------
# 割り算は機械語の Nat.div で高速に行い、その商を実行時の比較で検査する。
# 検査に落ちたときは安全側の値に倒す（実際には起きない）。健全性の証明は
# 割り算の正しさに依存せず、この検査だけに依存する。

def fl.pick(b: Bool, q: Nat) -> Nat:
  match b:
    case True{}:
      q
    case False{}:
      0n

# a / d の切り下げ（d * fl(a, d) <= a を満たす）
def fl(+a: Nat, +d: Nat) -> Nat:
  +q = Nat.div(a, d)
  fl.pick(Nat.is_le(Nat.mul(d, q), a), q)

def cl.pick(b: Bool, q: Nat, a: Nat) -> Nat:
  match b:
    case True{}:
      q
    case False{}:
      a

def cl.pick1(b: Bool, +q: Nat, +a: Nat, +d: Nat) -> Nat:
  match b:
    case True{}:
      q
    case False{}:
      cl.pick(Nat.is_le(a, Nat.mul(d, 1n+q)), 1n+q, a)

# a / d の切り上げ（d >= 1 なら a <= d * cl(a, d) を満たす）
def cl(+a: Nat, +d: Nat) -> Nat:
  +q = Nat.div(a, d)
  cl.pick1(Nat.is_le(a, Nat.mul(d, q)), q, a, d)

# x を分母 2^t の二進有理数に下向き丸め（p は切り下げ、n は切り上げ）
def Dy.down(x: Dy, +t: Nat) -> Dy:
  match x:
    case Dy{z, +k}:
      match z:
        case Z{p, n}:
          Dy{Z{fl(Nat.mul(pow2(t), p), pow2(k)), cl(Nat.mul(pow2(t), n), pow2(k))}, t}

# x を分母 2^t の二進有理数に上向き丸め
def Dy.up(x: Dy, +t: Nat) -> Dy:
  match x:
    case Dy{z, +k}:
      match z:
        case Z{p, n}:
          Dy{Z{cl(Nat.mul(pow2(t), p), pow2(k)), fl(Nat.mul(pow2(t), n), pow2(k))}, t}

# Intervals
# ---------

# 閉区間 [lo, hi]
type Iv is Data:
  Iv{lo: Dy, hi: Dy}

# 加算（端点を分母 2^t へ外向きに丸める）
def Iv.add(a: Iv, b: Iv, +t: Nat) -> Iv:
  match a b:
    case Iv{alo, ahi} Iv{blo, bhi}:
      Iv{Dy.down(Dy.add(alo, blo), t), Dy.up(Dy.add(ahi, bhi), t)}

# 乗算：4つの端点積の最小・最大を外向きに丸める
def Iv.mul(a: Iv, b: Iv, +t: Nat) -> Iv:
  match a b:
    case Iv{+alo, +ahi} Iv{+blo, +bhi}:
      +p1 = Dy.mul(alo, blo)
      +p2 = Dy.mul(alo, bhi)
      +p3 = Dy.mul(ahi, blo)
      +p4 = Dy.mul(ahi, bhi)
      Iv{Dy.down(Dy.min(Dy.min(p1, p2), Dy.min(p3, p4)), t), Dy.up(Dy.max(Dy.max(p1, p2), Dy.max(p3, p4)), t)}

# 符号反転（丸め不要）
def Iv.neg(a: Iv) -> Iv:
  match a:
    case Iv{lo, hi}:
      Iv{Dy.neg(hi), Dy.neg(lo)}

# 減算
def Iv.sub(a: Iv, b: Iv, +t: Nat) -> Iv:
  Iv.add(a, Iv.neg(b), t)

# Constructors and display
# ------------------------

# (p - n) / 2^k
def dy(p: Nat, n: Nat, k: Nat) -> Dy:
  Dy{Z{p, n}, k}

def iv(lo: Dy, hi: Dy) -> Iv:
  Iv{lo, hi}

# 小数部 r/den を i 桁だけ切り捨てで表示
def Dy.show.frac(i: Nat, +r: Nat, +den: Nat) -> String:
  match i:
    case 0n:
      ""
    case 1n+j:
      +w = Nat.mul(10n, r)
      Nat.show(Nat.div(w, den)) ++ Dy.show.frac(j, Nat.mod(w, den), den)

def Dy.show.abs(+s: String, +m: Nat, +k: Nat) -> String:
  +d = pow2(k)
  s ++ Nat.show(m) ++ "/2^" ++ Nat.show(k) ++ " (" ++ s ++ Nat.show(Nat.div(m, d)) ++ "." ++ Dy.show.frac(6n, Nat.mod(m, d), d) ++ ")"

def Dy.show.sign(b: Bool, +p: Nat, +n: Nat, +k: Nat) -> String:
  match b:
    case True{}:
      Dy.show.abs("", Nat.sub(p, n), k)
    case False{}:
      Dy.show.abs("-", Nat.sub(n, p), k)

# 表示専用：m/2^k と、その小数表示（小数第6位で切り捨て）
def Dy.show(x: Dy) -> String:
  match x:
    case Dy{z, +k}:
      match z:
        case Z{+p, +n}:
          Dy.show.sign(Nat.is_ge(p, n), p, n, k)

def Iv.show(a: Iv) -> String:
  match a:
    case Iv{lo, hi}:
      "[" ++ Dy.show(lo) ++ ", " ++ Dy.show(hi) ++ "]"
