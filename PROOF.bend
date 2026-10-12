# 8パズルの法則 (LAWS.bend) の証明。
#
# 議論の骨組み:
#   1. 左右の手はタイルの列を変えない。上下の手は列の 3 要素を回転させる
#      (x a b -> a b x、またはその逆)。
#   2. 回転しても「全部異なる」は変わらない (dist_rot)。
#      全部異なるなら、転倒数の偶奇も変わらない (par_rot):
#      x が a, b を飛び越すと、x と a, x と b の大小関係が 2 つ反転するだけ。
#   3. よって odd(b) はどの手でも不変 (step_inv)、どの手順でも不変 (run_inv)。
#   4. ゴールの odd は False。odd が True の盤面はゴールになれない。
#   5. 解ける盤面は、実際の手順を証拠として渡し、コンパイラが再生して確かめる。
#
# タクティクも自動証明もない。命題は型で、証明はその型の値 (def) である。

import Base
import ./main.bend as Pz
import ./LAWS.bend as Laws

# 道具
# ----
# T(b): b が True なら Unit (証明あり)、False なら Empty (証明なし)

def T(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def to_T(-c: Bool, h: {True{} == c : Bool}) -> T(c):
  %h : T(_)
  Unit{}

def and_l(+a: Bool, -b: Bool, w: T(Bool.and(a, b))) -> T(a):
  match a:
    case True{}:
      Unit{}
    case False{}:
      w

def and_r(+a: Bool, -b: Bool, w: T(Bool.and(a, b))) -> T(b):
  match a:
    case True{}:
      w
    case False{}:
      Empty.absurd(T(b), w)

def and_cond(+c: Bool, -x: Bool, -y: Bool, f: T(c) -> {x == y : Bool})
  -> {Bool.and(c, x) == Bool.and(c, y) : Bool}:
  match c:
    case True{}:
      f(Unit{})
    case False{}:
      {==}

def and_false(c: Bool) -> {Bool.and(c, False{}) == False{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def bool_case(+b: Bool, -P: Bool -> Type,
  t: {True{} == b : Bool} -> P(True{}),
  f: {False{} == b : Bool} -> P(False{})) -> P(b):
  match b:
    case True{}:
      t({==})
    case False{}:
      f({==})

# 自然数の比較についての事実
# ------------------------

def eq_sym(x: Nat, a: Nat) -> {Pz.nat_eq(x, a) == Pz.nat_eq(a, x) : Bool}:
  match x a:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      eq_sym(p, q)

def eq_sound(+x: Nat, +a: Nat, w: T(Pz.nat_eq(x, a))) -> {x == a : Nat}:
  match x a:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, w)
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, w)
    case 1n+p 1n+q:
      %eq_sound(p, q, w) : {1n+p == 1n+_ : Nat}
      {==}

# 三分律: x と a が違うなら、「a < x」は「x < a でない」と同じ
def trich(x: Nat, a: Nat, h: T(Bool.not(Pz.nat_eq(x, a))))
  -> {Bool.not(Pz.nat_lt(x, a)) == Pz.nat_lt(a, x) : Bool}:
  match x a:
    case 0n 0n:
      Empty.absurd({Bool.not(Pz.nat_lt(0n, 0n)) == Pz.nat_lt(0n, 0n) : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      trich(p, q, h)

# 総当たりで示すブール恒等式 (自動生成)
# ----------------------------------

# 転倒数の偶奇: x が a, b を飛び越しても xor は変わらない (全 128 通りを計算)
def par_core(ba: Bool, xa: Bool, xb: Bool, sa: Bool, sb: Bool, sx: Bool, os: Bool)
  -> {Bool.xor(Bool.xor(Bool.not(xa), Bool.xor(Bool.not(xb), sx)), Bool.xor(Bool.xor(ba, sa), Bool.xor(sb, os)))
     == Bool.xor(Bool.xor(ba, Bool.xor(xa, sa)), Bool.xor(Bool.xor(xb, sb), Bool.xor(sx, os))) : Bool}:
  match ba xa xb sa sb sx os:
    case True{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} False{}:
      {==}

# 相異なること: 並べ替えても and は変わらない (全 128 通り)
def dis_core(xa: Bool, xb: Bool, ab: Bool, fa: Bool, fb: Bool, fx: Bool, ds: Bool)
  -> {Bool.and(Bool.and(Bool.not(xa), Bool.and(Bool.not(xb), fx)), Bool.and(Bool.and(Bool.not(ab), fa), Bool.and(fb, ds)))
     == Bool.and(Bool.and(Bool.not(ab), Bool.and(Bool.not(xa), fa)), Bool.and(Bool.and(Bool.not(xb), fb), Bool.and(fx, ds))) : Bool}:
  match xa xb ab fa fb fx ds:
    case True{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} False{}:
      {==}

# h が x, a, b のどれとも違うこと: 順番によらない (全 16 通り)
def fresh_core(hx: Bool, ha: Bool, hb: Bool, f: Bool)
  -> {Bool.and(Bool.not(hx), Bool.and(Bool.not(ha), Bool.and(Bool.not(hb), f)))
     == Bool.and(Bool.not(ha), Bool.and(Bool.not(hb), Bool.and(Bool.not(hx), f))) : Bool}:
  match hx ha hb f:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

# h より小さいものの個数の偶奇: 順番によらない (全 16 通り)
def small_core(hx: Bool, ha: Bool, hb: Bool, s: Bool)
  -> {Bool.xor(hx, Bool.xor(ha, Bool.xor(hb, s)))
     == Bool.xor(ha, Bool.xor(hb, Bool.xor(hx, s))) : Bool}:
  match hx ha hb s:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

# 回転は不変量を保つ
# ----------------

def fresh_rot(+k: Nat, +h: Nat, +l: List<&2, Nat>)
  -> {Pz.fresh(h, l) == Pz.fresh(h, Pz.rot(k, l)) : Bool}:
  match k l:
    case 0n Nil{}:
      {==}
    case 0n Con{x, Nil{}}:
      {==}
    case 0n Con{x, Con{a, Nil{}}}:
      {==}
    case 0n Con{x, Con{a, Con{b, s}}}:
      fresh_core(Pz.nat_eq(h, x), Pz.nat_eq(h, a), Pz.nat_eq(h, b), Pz.fresh(h, s))
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{v, t}:
      %fresh_rot(p, h, t) : {Pz.fresh(h, v <> t) == Bool.and(Bool.not(Pz.nat_eq(h, v)), _) : Bool}
      {==}

def small_rot(+k: Nat, +h: Nat, +l: List<&2, Nat>)
  -> {Pz.smaller(h, l) == Pz.smaller(h, Pz.rot(k, l)) : Bool}:
  match k l:
    case 0n Nil{}:
      {==}
    case 0n Con{x, Nil{}}:
      {==}
    case 0n Con{x, Con{a, Nil{}}}:
      {==}
    case 0n Con{x, Con{a, Con{b, s}}}:
      small_core(Pz.nat_lt(x, h), Pz.nat_lt(a, h), Pz.nat_lt(b, h), Pz.smaller(h, s))
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{v, t}:
      %small_rot(p, h, t) : {Pz.smaller(h, v <> t) == Bool.xor(Pz.nat_lt(v, h), _) : Bool}
      {==}

def dist_rot(+k: Nat, +l: List<&2, Nat>)
  -> {Pz.distinct(l) == Pz.distinct(Pz.rot(k, l)) : Bool}:
  match k l:
    case 0n Nil{}:
      {==}
    case 0n Con{x, Nil{}}:
      {==}
    case 0n Con{x, Con{a, Nil{}}}:
      {==}
    case 0n Con{x, Con{a, Con{b, s}}}:
      %eq_sym(x, a) : {Pz.distinct(x <> a <> b <> s)
        == Bool.and(Bool.and(Bool.not(Pz.nat_eq(a, b)), Bool.and(Bool.not(_), Pz.fresh(a, s))),
                    Pz.distinct(b <> x <> s)) : Bool}
      %eq_sym(x, b) : {Pz.distinct(x <> a <> b <> s)
        == Bool.and(Bool.and(Bool.not(Pz.nat_eq(a, b)), Bool.and(Bool.not(Pz.nat_eq(x, a)), Pz.fresh(a, s))),
                    Bool.and(Bool.and(Bool.not(_), Pz.fresh(b, s)), Pz.distinct(x <> s))) : Bool}
      dis_core(Pz.nat_eq(x, a), Pz.nat_eq(x, b), Pz.nat_eq(a, b),
        Pz.fresh(a, s), Pz.fresh(b, s), Pz.fresh(x, s), Pz.distinct(s))
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{v, t}:
      %fresh_rot(p, v, t) : {Pz.distinct(v <> t) == Bool.and(_, Pz.distinct(Pz.rot(p, t))) : Bool}
      %dist_rot(p, t) : {Pz.distinct(v <> t) == Bool.and(Pz.fresh(v, t), _) : Bool}
      {==}

def par_rot(+k: Nat, +l: List<&2, Nat>, +d: T(Pz.distinct(l)))
  -> {Pz.odd_inv(l) == Pz.odd_inv(Pz.rot(k, l)) : Bool}:
  match k l:
    case 0n Nil{}:
      {==}
    case 0n Con{x, Nil{}}:
      {==}
    case 0n Con{x, Con{a, Nil{}}}:
      {==}
    case 0n Con{x, Con{a, Con{b, s}}}:
      +fx = and_l(Pz.fresh(x, a <> b <> s), Pz.distinct(a <> b <> s), d)
      h1 = and_l(Bool.not(Pz.nat_eq(x, a)), Pz.fresh(x, b <> s), fx)
      h2 = and_l(Bool.not(Pz.nat_eq(x, b)), Pz.fresh(x, s),
        and_r(Bool.not(Pz.nat_eq(x, a)), Pz.fresh(x, b <> s), fx))
      %trich(x, a, h1) : {Bool.xor(Bool.xor(_, Bool.xor(Pz.nat_lt(b, x), Pz.smaller(x, s))), Pz.odd_inv(a <> b <> s))
        == Pz.odd_inv(a <> b <> x <> s) : Bool}
      %trich(x, b, h2) : {Bool.xor(Bool.xor(Bool.not(Pz.nat_lt(x, a)), Bool.xor(_, Pz.smaller(x, s))), Pz.odd_inv(a <> b <> s))
        == Pz.odd_inv(a <> b <> x <> s) : Bool}
      par_core(Pz.nat_lt(b, a), Pz.nat_lt(x, a), Pz.nat_lt(x, b),
        Pz.smaller(a, s), Pz.smaller(b, s), Pz.smaller(x, s), Pz.odd_inv(s))
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{v, t}:
      dt = and_r(Pz.fresh(v, t), Pz.distinct(t), d)
      %small_rot(p, v, t) : {Pz.odd_inv(v <> t) == Bool.xor(_, Pz.odd_inv(Pz.rot(p, t))) : Bool}
      %par_rot(p, t, dt) : {Pz.odd_inv(v <> t) == Bool.xor(Pz.smaller(v, t), _) : Bool}
      {==}

def oddl_rot(+k: Nat, +l: List<&2, Nat>)
  -> {Pz.odd_list(l) == Pz.odd_list(Pz.rot(k, l)) : Bool}:
  %dist_rot(k, l) : {Bool.and(Pz.distinct(l), Pz.odd_inv(l)) == Bool.and(_, Pz.odd_inv(Pz.rot(k, l))) : Bool}
  and_cond(Pz.distinct(l), Pz.odd_inv(l), Pz.odd_inv(Pz.rot(k, l)), d => par_rot(k, l, d))

# 逆回転は回転で打ち消せるので、同じく不変量を保つ
def rot_unrot(+k: Nat, +l: List<&2, Nat>)
  -> {l == Pz.rot(k, Pz.unrot(k, l)) : List<&2, Nat>}:
  match k l:
    case 0n Nil{}:
      {==}
    case 0n Con{x, Nil{}}:
      {==}
    case 0n Con{x, Con{a, Nil{}}}:
      {==}
    case 0n Con{x, Con{a, Con{b, s}}}:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{v, t}:
      %rot_unrot(p, t) : {v <> t == v <> _ : List<&2, Nat>}
      {==}

def oddl_unrot(+k: Nat, +l: List<&2, Nat>)
  -> {Pz.odd_list(l) == Pz.odd_list(Pz.unrot(k, l)) : Bool}:
  %Equal.sym(List<&2, Nat>, l, Pz.rot(k, Pz.unrot(k, l)), rot_unrot(k, l))
    : {Pz.odd_list(_) == Pz.odd_list(Pz.unrot(k, l)) : Bool}
  Equal.sym(Bool, Pz.odd_list(Pz.unrot(k, l)), Pz.odd_list(Pz.rot(k, Pz.unrot(k, l))),
    oddl_rot(k, Pz.unrot(k, l)))

# 1 手で不変量は変わらない
# ----------------------

def up_case(c: Bool, +p: Nat, +ts: List<&2, Nat>)
  -> {Pz.odd_list(ts) == Pz.odd(Pz.pick(Pz.Board, c, Pz.Board{p, ts},
        Pz.Board{Nat.sub(p, 3n), Pz.rot(Nat.sub(p, 3n), ts)})) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      oddl_rot(Nat.sub(p, 3n), ts)

def down_case(c: Bool, +p: Nat, +ts: List<&2, Nat>)
  -> {Pz.odd_list(ts) == Pz.odd(Pz.pick(Pz.Board, c, Pz.Board{Nat.add(p, 3n), Pz.unrot(p, ts)},
        Pz.Board{p, ts})) : Bool}:
  match c:
    case True{}:
      oddl_unrot(p, ts)
    case False{}:
      {==}

def side_case(c: Bool, -p: Nat, -q: Nat, -ts: List<&2, Nat>)
  -> {Pz.odd_list(ts) == Pz.odd(Pz.pick(Pz.Board, c, Pz.Board{p, ts}, Pz.Board{q, ts})) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def step_inv(m: Pz.Move, +b: Pz.Board) -> {Pz.odd(b) == Pz.odd(Pz.step(m, b)) : Bool}:
  match m:
    case Pz.Up{}:
      match b:
        case Pz.Board{p, ts}:
          up_case(Pz.nat_lt(p, 3n), p, ts)
    case Pz.Down{}:
      match b:
        case Pz.Board{p, ts}:
          down_case(Pz.nat_lt(p, 6n), p, ts)
    case Pz.Left{}:
      match b:
        case Pz.Board{p, ts}:
          side_case(Pz.nat_eq(Pz.col(p), 0n), p, Nat.sub(p, 1n), ts)
    case Pz.Right{}:
      match b:
        case Pz.Board{p, ts}:
          side_case(Pz.nat_eq(Pz.col(p), 2n), p, Nat.add(p, 1n), ts)

# 何手指しても不変量は変わらない (手順の長さについての帰納法)
def run_inv(+moves: List<&2, Pz.Move>, +b: Pz.Board)
  -> {Pz.odd(b) == Pz.odd(Pz.run(moves, b)) : Bool}:
  match moves:
    case Nil{}:
      {==}
    case m <> ms:
      Equal.trans(Bool, Pz.odd(b), Pz.odd(Pz.step(m, b)), Pz.odd(Pz.run(ms, Pz.step(m, b))),
        step_inv(m, b), run_inv(ms, Pz.step(m, b)))

def Laws.parity_invariant(b, moves):
  Equal.sym(Bool, Pz.odd(b), Pz.odd(Pz.replay(b, moves)), run_inv(moves, b))

# ゴールは不変量を満たさない
# ------------------------

def list_sound(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +w: T(Pz.list_eq(xs, ys)))
  -> {xs == ys : List<&2, Nat>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      Empty.absurd({Nil{} == y <> yt : List<&2, Nat>}, w)
    case Con{x, xt} Nil{}:
      Empty.absurd({x <> xt == Nil{} : List<&2, Nat>}, w)
    case Con{x, xt} Con{y, yt}:
      %eq_sound(x, y, and_l(Pz.nat_eq(x, y), Pz.list_eq(xt, yt), w)) : {x <> xt == _ <> yt : List<&2, Nat>}
      %list_sound(xt, yt, and_r(Pz.nat_eq(x, y), Pz.list_eq(xt, yt), w)) : {x <> xt == x <> _ : List<&2, Nat>}
      {==}

# タイル列がゴールと一致するなら odd_list はゴールの値 (False) になり、矛盾
def le_false.hit(+ts: List<&2, Nat>, e: {Pz.odd_list(ts) == True{} : Bool},
  h: {True{} == Pz.list_eq(ts, Pz.goal_tiles()) : Bool}) -> {True{} == False{} : Bool}:
  same = list_sound(ts, Pz.goal_tiles(), to_T(Pz.list_eq(ts, Pz.goal_tiles()), h))
  %e : {_ == False{} : Bool}
  %Equal.sym(List<&2, Nat>, ts, Pz.goal_tiles(), same) : {Pz.odd_list(_) == False{} : Bool}
  {==}

def le_false(+ts: List<&2, Nat>, e: {Pz.odd_list(ts) == True{} : Bool})
  -> {Pz.list_eq(ts, Pz.goal_tiles()) == False{} : Bool}:
  bool_case(Pz.list_eq(ts, Pz.goal_tiles()), c => {c == False{} : Bool},
    h => le_false.hit(ts, e, h),
    h => {==})

def not_goal(+r: Pz.Board, e: {Pz.odd(r) == True{} : Bool})
  -> {Pz.is_goal(r) == False{} : Bool}:
  match r:
    case Pz.Board{p, ts}:
      %Equal.sym(Bool, Pz.list_eq(ts, Pz.goal_tiles()), False{}, le_false(ts, e))
        : {Bool.and(Pz.nat_eq(p, 8n), _) == False{} : Bool}
      and_false(Pz.nat_eq(p, 8n))

def Laws.odd_never_solved(b, e, moves):
  +r = Pz.replay(b, moves)
  inv = Laws.parity_invariant(b, moves)
  not_goal(r, Equal.trans(Bool, Pz.odd(r), Pz.odd(b), True{}, inv, e))

# 具体的な盤面
# -----------
# odd(swap78()) == True はコンパイラが計算して確かめる ({==})

def Laws.swap78_unsolvable(moves):
  Laws.odd_never_solved(Pz.swap78(), {==}, moves)

def Laws.odd_case_unsolvable(moves):
  Laws.odd_never_solved(Pz.odd_case(), {==}, moves)

# 解ける側は手順そのものが証拠。コンパイラが盤面を再生してゴールを確かめる
def Laws.hard_solvable():
  ([Pz.Up{}, Pz.Up{}, Pz.Left{}, Pz.Down{}, Pz.Down{}, Pz.Right{}, Pz.Right{}, Pz.Up{}, Pz.Up{}, Pz.Left{}, Pz.Down{}, Pz.Left{}, Pz.Down{}, Pz.Right{}, Pz.Right{}, Pz.Up{}, Pz.Up{}, Pz.Left{}, Pz.Down{}, Pz.Left{}, Pz.Down{}, Pz.Right{}, Pz.Right{}, Pz.Up{}, Pz.Up{}, Pz.Left{}, Pz.Left{}, Pz.Down{}, Pz.Down{}, Pz.Right{}, Pz.Right{}], {==})

def Laws.reversed_solvable():
  ([Pz.Up{}, Pz.Left{}, Pz.Up{}, Pz.Left{}, Pz.Down{}, Pz.Down{}, Pz.Right{}, Pz.Up{}, Pz.Up{}, Pz.Left{}, Pz.Down{}, Pz.Down{}, Pz.Right{}, Pz.Up{}, Pz.Up{}, Pz.Right{}, Pz.Down{}, Pz.Down{}, Pz.Left{}, Pz.Up{}, Pz.Up{}, Pz.Right{}, Pz.Down{}, Pz.Left{}, Pz.Up{}, Pz.Left{}, Pz.Down{}, Pz.Right{}, Pz.Down{}, Pz.Right{}], {==})
