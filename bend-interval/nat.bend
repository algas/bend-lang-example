# nat.bend: Nat の順序 LE と、加法・乗法の補題。
# 区間演算の証明はすべてここに帰着する。

import Base

# Order
# -----

# a <= b を型として表す（具体値では Unit / Empty に計算される）
def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n _:
      Unit
    case 1n+x 0n:
      Empty
    case 1n+x 1n+y:
      LE(x, y)

# Bool で選ぶ型：True{} == False{} を反駁するのに使う
def BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def le_refl(a: Nat) -> LE(a, a):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      le_refl(x)

def le_succ_r(a: Nat, b: Nat, e: LE(a, b)) -> LE(a, 1n+b):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(LE(x, 0n), e)
        case 1n+y:
          le_succ_r(x, y, e)

def le_trans(a: Nat, b: Nat, c: Nat, ab: LE(a, b), bc: LE(b, c)) -> LE(a, c):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(LE(1n+x, c), ab)
        case 1n+y:
          match c:
            case 0n:
              Empty.absurd(LE(1n+x, 0n), bc)
            case 1n+z:
              le_trans(x, y, z, ab, bc)

# 等式から順序を得る
def le_of_eq(a: Nat, b: Nat, e: {a == b : Nat}) -> LE(a, b):
  %e : LE(a, _)
  le_refl(a)

# 実行時の比較 Nat.is_le が True なら LE が成り立つ（反映補題）
def le_of_is_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> LE(a, b):
  match a b:
    case 0n _:
      Unit{}
    case 1n+x 0n:
      %e : BD(_, Empty, Unit)
      Unit{}
    case 1n+x 1n+y:
      le_of_is_le(x, y, e)

# Addition
# --------

def add_zero(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      %add_zero(b) : {b == _ : Nat}
      {==}
    case 1n+p:
      %add_succ(b, p) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# a + (b + c) == b + (a + c)
def add_swap(x: Nat, +y: Nat, +z: Nat) -> {Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      %add_succ(y, Nat.add(q, z)) : {1n+Nat.add(q, Nat.add(y, z)) == _ : Nat}
      %add_swap(q, y, z) : {1n+Nat.add(q, Nat.add(y, z)) == 1n+_ : Nat}
      {==}

# b <= a + b
def le_add_l(a: Nat, +b: Nat) -> LE(b, Nat.add(a, b)):
  match a:
    case 0n:
      le_refl(b)
    case 1n++p:
      le_succ_r(b, Nat.add(p, b), le_add_l(p, b))

# a <= a + b
def le_add_r(+a: Nat, +b: Nat) -> LE(a, Nat.add(a, b)):
  %add_comm(b, a) : LE(a, _)
  le_add_l(b, a)

# a <= b, c <= d ならば a + c <= b + d
def add_mono(a: Nat, +b: Nat, +c: Nat, +d: Nat, ab: LE(a, b), cd: LE(c, d)) -> LE(Nat.add(a, c), Nat.add(b, d)):
  match a b:
    case 0n _:
      le_trans(c, d, Nat.add(b, d), cd, le_add_l(b, d))
    case 1n+x 0n:
      Empty.absurd(LE(Nat.add(1n+x, c), Nat.add(0n, d)), ab)
    case 1n+x 1n+y:
      add_mono(x, y, c, d, ab, cd)

# m + x <= m + y ならば x <= y
def add_cancel(m: Nat, -x: Nat, -y: Nat, e: LE(Nat.add(m, x), Nat.add(m, y))) -> LE(x, y):
  match m:
    case 0n:
      e
    case 1n+p:
      add_cancel(p, x, y, e)

# 両辺を等式で書き換える
def le_rw(-a: Nat, -b: Nat, -c: Nat, -d: Nat, ea: {a == c : Nat}, eb: {b == d : Nat}, e: LE(a, b)) -> LE(c, d):
  %ea : LE(_, d)
  %eb : LE(a, _)
  e

# x + m <= y + m ならば x <= y
def add_cancel_r(+m: Nat, +x: Nat, +y: Nat, e: LE(Nat.add(x, m), Nat.add(y, m))) -> LE(x, y):
  add_cancel(m, x, y, le_rw(Nat.add(x, m), Nat.add(y, m), Nat.add(m, x), Nat.add(m, y), add_comm(x, m), add_comm(y, m), e))

# Multiplication
# --------------

def mul_zero(a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

def mul_succ(+a: Nat, +b: Nat) -> {Nat.add(a, Nat.mul(a, b)) == Nat.mul(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %mul_succ(p, b) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+Nat.add(b, _) : Nat}
      %add_swap(p, b, Nat.mul(p, b)) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+_ : Nat}
      {==}

def mul_comm(+a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      %mul_zero(b) : {_ == Nat.mul(b, 0n) : Nat}
      {==}
    case 1n++p:
      %mul_succ(b, p) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

# (a + b) c == a c + b c
def mul_dist_r(a: Nat, -b: Nat, +c: Nat) -> {Nat.add(Nat.mul(a, c), Nat.mul(b, c)) == Nat.mul(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mul_dist_r(p, b, c) : {Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) == Nat.add(c, _) : Nat}
      %add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)) : {_ == Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))) : Nat}
      {==}

# a (b + c) == a b + a c
def mul_dist_l(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  %mul_comm(b, a) : {Nat.mul(a, Nat.add(b, c)) == Nat.add(_, Nat.mul(a, c)) : Nat}
  %mul_comm(c, a) : {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(b, a), _) : Nat}
  %mul_comm(Nat.add(b, c), a) : {_ == Nat.add(Nat.mul(b, a), Nat.mul(c, a)) : Nat}
  Equal.sym(Nat, Nat.add(Nat.mul(b, a), Nat.mul(c, a)), Nat.mul(Nat.add(b, c), a), mul_dist_r(b, c, a))

# (a b) c == a (b c)
def mul_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %mul_dist_r(b, Nat.mul(p, b), c) : {_ == Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) : Nat}
      %mul_assoc(p, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

# a <= b ならば a c <= b c
def mul_mono(+a: Nat, +b: Nat, +c: Nat, ab: LE(a, b)) -> LE(Nat.mul(a, c), Nat.mul(b, c)):
  match a b:
    case 0n _:
      Unit{}
    case 1n+x 0n:
      Empty.absurd(LE(Nat.mul(1n+x, c), 0n), ab)
    case 1n+x 1n+y:
      add_mono(c, c, Nat.mul(x, c), Nat.mul(y, c), le_refl(c), mul_mono(x, y, c, ab))

# a <= b ならば c a <= c b
def mul_mono_l(+c: Nat, +a: Nat, +b: Nat, ab: LE(a, b)) -> LE(Nat.mul(c, a), Nat.mul(c, b)):
  le_rw(Nat.mul(a, c), Nat.mul(b, c), Nat.mul(c, a), Nat.mul(c, b), mul_comm(a, c), mul_comm(b, c), mul_mono(a, b, c, ab))

# a (1+c) <= b (1+c) ならば a <= b
def mul_cancel(+a: Nat, +b: Nat, +c: Nat, e: LE(Nat.mul(a, 1n+c), Nat.mul(b, 1n+c))) -> LE(a, b):
  match a b:
    case 0n _:
      Unit{}
    case 1n+x 0n:
      Empty.absurd(LE(1n+x, 0n), e)
    case 1n+x 1n+y:
      mul_cancel(x, y, c, add_cancel(1n+c, Nat.mul(x, 1n+c), Nat.mul(y, 1n+c), e))

# (1+c) a <= (1+c) b ならば a <= b
def mul_cancel_l(+c: Nat, +a: Nat, +b: Nat, e: LE(Nat.mul(1n+c, a), Nat.mul(1n+c, b))) -> LE(a, b):
  mul_cancel(a, b, c, le_rw(Nat.mul(1n+c, a), Nat.mul(1n+c, b), Nat.mul(a, 1n+c), Nat.mul(b, 1n+c), mul_comm(1n+c, a), mul_comm(1n+c, b), e))

# More rearrangements
# -------------------

# (a + b) + (c + d) == (a + c) + (b + d)
def add4_m(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %add_assoc(a, b, Nat.add(c, d)) : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %add_assoc(a, c, Nat.add(b, d)) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %add_swap(b, c, d) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == Nat.add(a, _) : Nat}
  {==}

# (a + b) + (c + d) == (a + d) + (c + b)
def add4_x(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, d), Nat.add(c, b)) : Nat}:
  %add_comm(d, c) : {Nat.add(Nat.add(a, b), _) == Nat.add(Nat.add(a, d), Nat.add(c, b)) : Nat}
  %add_comm(b, c) : {Nat.add(Nat.add(a, b), Nat.add(d, c)) == Nat.add(Nat.add(a, d), _) : Nat}
  add4_m(a, b, d, c)

# (a + b) + (c + d) == (c + b) + (a + d)
def add4_y(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(c, b), Nat.add(a, d)) : Nat}:
  %add_comm(b, a) : {Nat.add(_, Nat.add(c, d)) == Nat.add(Nat.add(c, b), Nat.add(a, d)) : Nat}
  %add_comm(b, c) : {Nat.add(Nat.add(b, a), Nat.add(c, d)) == Nat.add(_, Nat.add(a, d)) : Nat}
  add4_m(b, a, c, d)

# a (b c) == (a b) c
def mul_assoc_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(Nat.mul(a, b), c) : Nat}:
  Equal.sym(Nat, Nat.mul(Nat.mul(a, b), c), Nat.mul(a, Nat.mul(b, c)), mul_assoc(a, b, c))

# a (b c) == b (a c)
def mul_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(b, Nat.mul(a, c)) : Nat}:
  %mul_assoc(a, b, c) : {_ == Nat.mul(b, Nat.mul(a, c)) : Nat}
  %mul_assoc(b, a, c) : {Nat.mul(Nat.mul(a, b), c) == _ : Nat}
  %mul_comm(a, b) : {Nat.mul(Nat.mul(a, b), c) == Nat.mul(_, c) : Nat}
  {==}

# a b + a c == a (b + c)
def mul_dist_l_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == Nat.mul(a, Nat.add(b, c)) : Nat}:
  Equal.sym(Nat, Nat.mul(a, Nat.add(b, c)), Nat.add(Nat.mul(a, b), Nat.mul(a, c)), mul_dist_l(a, b, c))

def zero_mul_r(d: Nat) -> {0n == Nat.mul(d, 0n) : Nat}:
  Equal.sym(Nat, Nat.mul(d, 0n), 0n, mul_zero(d))

# 1 <= m, m x <= m y ならば x <= y
def mul_cancel_pos(m: Nat, pos: LE(1n, m), +x: Nat, +y: Nat, e: LE(Nat.mul(m, x), Nat.mul(m, y))) -> LE(x, y):
  match m:
    case 0n:
      Empty.absurd(LE(x, y), pos)
    case 1n++c:
      mul_cancel_l(c, x, y, e)

# 1 <= d ならば a <= d a
def le_mul_pos(+a: Nat, d: Nat, pos: LE(1n, d)) -> LE(a, Nat.mul(d, a)):
  match d:
    case 0n:
      Empty.absurd(LE(a, 0n), pos)
    case 1n+c:
      le_add_r(a, Nat.mul(c, a))

# For multiplication
# ------------------

# b <= a ならば (a - b) + b == a
def sub_add(a: Nat, b: Nat, h: LE(b, a)) -> {Nat.add(Nat.sub(a, b), b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.add(0n, 1n+bp) == 0n : Nat}, h)
    case 1n+ap 0n:
      Equal.sym(Nat, 1n+ap, Nat.add(1n+ap, 0n), add_zero(1n+ap))
    case 1n++ap 1n++bp:
      %add_succ(Nat.sub(ap, bp), bp) : {_ == 1n+ap : Nat}
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(Nat.sub(ap, bp), bp), ap, sub_add(ap, bp, h))

# (A + (B + C)) + D == B + (C + (D + A))
def four(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, Nat.add(b, c)), d) == Nat.add(b, Nat.add(c, Nat.add(d, a))) : Nat}:
  %add_assoc(a, Nat.add(b, c), d) : {_ == Nat.add(b, Nat.add(c, Nat.add(d, a))) : Nat}
  %add_assoc(b, c, d) : {Nat.add(a, _) == Nat.add(b, Nat.add(c, Nat.add(d, a))) : Nat}
  %add_swap(b, a, Nat.add(c, d)) : {_ == Nat.add(b, Nat.add(c, Nat.add(d, a))) : Nat}
  %add_swap(c, a, d) : {Nat.add(b, _) == Nat.add(b, Nat.add(c, Nat.add(d, a))) : Nat}
  %add_comm(d, a) : {Nat.add(b, Nat.add(c, _)) == Nat.add(b, Nat.add(c, Nat.add(d, a))) : Nat}
  {==}

# 実行時の比較 Nat.is_le が False なら逆向きの LE が成り立つ
def le_of_not_is_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == False{} : Bool}) -> LE(b, a):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n 1n+y:
      %e : BD(_, Unit, Empty)
      Unit{}
    case 1n+x 0n:
      Unit{}
    case 1n+x 1n+y:
      le_of_not_is_le(x, y, e)

# 全順序
def le_total(a: Nat, b: Nat) -> LE(a, b) | LE(b, a):
  match a b:
    case 0n _:
      Inl{Unit{}}
    case 1n+x 0n:
      Inr{Unit{}}
    case 1n+x 1n+y:
      le_total(x, y)

# m (k p) == (k m) p
def mul_swap_assoc(+m: Nat, +k: Nat, +p: Nat) -> {Nat.mul(m, Nat.mul(k, p)) == Nat.mul(Nat.mul(k, m), p) : Nat}:
  %mul_assoc_r(k, m, p) : {Nat.mul(m, Nat.mul(k, p)) == _ : Nat}
  mul_swap(m, k, p)

# b1 (m a1) + b2 (m a2) == m (b1 a1 + b2 a2)
def mul_pull(+m: Nat, +b1: Nat, +a1: Nat, +b2: Nat, +a2: Nat) -> {Nat.add(Nat.mul(b1, Nat.mul(m, a1)), Nat.mul(b2, Nat.mul(m, a2))) == Nat.mul(m, Nat.add(Nat.mul(b1, a1), Nat.mul(b2, a2))) : Nat}:
  %mul_dist_l_r(m, Nat.mul(b1, a1), Nat.mul(b2, a2)) : {Nat.add(Nat.mul(b1, Nat.mul(m, a1)), Nat.mul(b2, Nat.mul(m, a2))) == _ : Nat}
  %mul_swap(m, b1, a1) : {Nat.add(_, Nat.mul(b2, Nat.mul(m, a2))) == Nat.add(Nat.mul(m, Nat.mul(b1, a1)), Nat.mul(m, Nat.mul(b2, a2))) : Nat}
  %mul_swap(m, b2, a2) : {Nat.add(Nat.mul(m, Nat.mul(b1, a1)), _) == Nat.add(Nat.mul(m, Nat.mul(b1, a1)), Nat.mul(m, Nat.mul(b2, a2))) : Nat}
  {==}

# x1 y1 + x2 y2 == y1 x1 + y2 x2
def comm2(+x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat) -> {Nat.add(Nat.mul(x1, y1), Nat.mul(x2, y2)) == Nat.add(Nat.mul(y1, x1), Nat.mul(y2, x2)) : Nat}:
  %mul_comm(x1, y1) : {Nat.add(Nat.mul(x1, y1), Nat.mul(x2, y2)) == Nat.add(_, Nat.mul(y2, x2)) : Nat}
  %mul_comm(x2, y2) : {Nat.add(Nat.mul(x1, y1), Nat.mul(x2, y2)) == Nat.add(Nat.mul(x1, y1), _) : Nat}
  {==}

# x1 y1 + x2 y2 == y2 x2 + y1 x1
def comm2x(+x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat) -> {Nat.add(Nat.mul(x1, y1), Nat.mul(x2, y2)) == Nat.add(Nat.mul(y2, x2), Nat.mul(y1, x1)) : Nat}:
  %add_comm(Nat.mul(y1, x1), Nat.mul(y2, x2)) : {Nat.add(Nat.mul(x1, y1), Nat.mul(x2, y2)) == _ : Nat}
  comm2(x1, y1, x2, y2)
