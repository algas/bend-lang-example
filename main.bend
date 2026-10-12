# 8パズル 可解性プルーバー (Bend 2)
#
# 盤面は「空きマスの位置」と「空きマスを除いたタイルを左上から読んだ列」で表す。
#   ゴール:  1 2 3
#            4 5 6
#            7 8 .     = Board{8n, [1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n]}
#
# 手 (Move) は空きマスが動く方向。盤外へ出る手は「何も起きない」とする。
# この表現では
#   - 左右の手はタイルの列を変えない (空きマスの位置だけ変わる)
#   - 上下の手は 1 枚のタイルが隣の 2 枚を飛び越す (列の 3 要素の回転)
# となり、LAWS.bend の「転倒数の偶奇は不変」がそのまま証明しやすい形になる。
#
#   bend main.bend      ソルバーを実行
#   bend PROOF.bend     法則 (LAWS.bend) の証明をチェック

import Base

type Move is Data:
  Up{}
  Down{}
  Left{}
  Right{}

type Board is Data:
  Board{blank: Nat, tiles: List<&2, Nat>}

# 比較 (証明しやすいよう素朴な再帰で定義)
# ----

def nat_eq(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+q:
      False{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      nat_eq(p, q)

def nat_lt(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      False{}
    case 0n 1n+q:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      nat_lt(p, q)

def pick(-A: Type, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# 手
# --

# 列の k 番目から始まる 3 要素を回転: x a b -> a b x (タイル x が下へ)
def rot(k: Nat, l: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      match l:
        case x <> a <> b <> s:
          a <> b <> x <> s
        case _:
          l
    case 1n+p:
      match l:
        case Nil{}:
          Nil{}
        case h <> t:
          h <> rot(p, t)

# 逆回転: a b x -> x a b (タイル x が上へ)
def unrot(k: Nat, l: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      match l:
        case a <> b <> x <> s:
          x <> a <> b <> s
        case _:
          l
    case 1n+p:
      match l:
        case Nil{}:
          Nil{}
        case h <> t:
          h <> unrot(p, t)

# 空きマスを (列 0 なら) 動かせない左、(列 2 なら) 動かせない右
def col(+p: Nat) -> Nat:
  Nat.mod(p, 3n)

def step(m: Move, b: Board) -> Board:
  match m:
    case Up{}:
      Board{+p, +ts} = b
      pick(Board, nat_lt(p, 3n), Board{p, ts}, Board{Nat.sub(p, 3n), rot(Nat.sub(p, 3n), ts)})
    case Down{}:
      Board{+p, +ts} = b
      pick(Board, nat_lt(p, 6n), Board{Nat.add(p, 3n), unrot(p, ts)}, Board{p, ts})
    case Left{}:
      Board{+p, +ts} = b
      pick(Board, nat_eq(col(p), 0n), Board{p, ts}, Board{Nat.sub(p, 1n), ts})
    case Right{}:
      Board{+p, +ts} = b
      pick(Board, nat_eq(col(p), 2n), Board{p, ts}, Board{Nat.add(p, 1n), ts})

# 手の列を最初から順に適用 (縮む引数を先頭に)
def run(moves: List<&2, Move>, b: Board) -> Board:
  match moves:
    case Nil{}:
      b
    case m <> ms:
      run(ms, step(m, b))

def replay(b: Board, moves: List<&2, Move>) -> Board:
  run(moves, b)

# ゴール判定
# ---------

def list_eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}
    case Con{x, xt} Con{y, yt}:
      nat_eq(x, y) && list_eq(xt, yt)

def goal_tiles() -> List<&2, Nat>:
  [1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n]

def is_goal(b: Board) -> Bool:
  Board{p, ts} = b
  nat_eq(p, 8n) && list_eq(ts, goal_tiles())

# 不変量: 転倒数の偶奇
# -------------------
# smaller(h, l): l の中で h より小さいものの個数の偶奇 (xor で数える)
# odd_inv(l):    l の転倒数が奇数か
# distinct(l):   l の要素が全部異なるか
# odd(b):        distinct かつ 転倒数が奇数 (LAWS.bend の不変量)

def smaller(+h: Nat, l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case v <> t:
      Bool.xor(nat_lt(v, h), smaller(h, t))

def odd_inv(l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case +h <> +t:
      Bool.xor(smaller(h, t), odd_inv(t))

def fresh(+h: Nat, l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case v <> t:
      Bool.not(nat_eq(h, v)) && fresh(h, t)

def distinct(l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case +h <> +t:
      fresh(h, t) && distinct(t)

def odd_list(+l: List<&2, Nat>) -> Bool:
  distinct(l) && odd_inv(l)

def odd(b: Board) -> Bool:
  Board{p, ts} = b
  odd_list(ts)

# 表示用: 転倒数そのもの
def count_smaller(+h: Nat, l: List<&2, Nat>) -> Nat:
  match l:
    case Nil{}:
      0n
    case v <> t:
      Nat.add(pick(Nat, nat_lt(v, h), 1n, 0n), count_smaller(h, t))

def inversions(l: List<&2, Nat>) -> Nat:
  match l:
    case Nil{}:
      0n
    case +h <> +t:
      Nat.add(count_smaller(h, t), inversions(t))

# 9 マスの並び (0 = 空き) から盤面を作る
# -------------------------------------

def index_of0(l: List<&2, Nat>) -> Nat:
  match l:
    case Nil{}:
      0n
    case h <> t:
      pick(Nat, nat_eq(h, 0n), 0n, 1n+index_of0(t))

def drop0(l: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Nil{}:
      Nil{}
    case +h <> +t:
      pick(List<&2, Nat>, nat_eq(h, 0n), drop0(t), h <> drop0(t))

def from_grid(+cells: List<&2, Nat>) -> Board:
  Board{index_of0(cells), drop0(cells)}

# ソルバー: 反復深化 DFS + マンハッタン距離で枝刈り
# ----------------------------------------------

# 探索中に何度も計算するので、距離は機械語の整数 (U32) で求める
def absdiff(+a: U32, +b: U32) -> U32:
  pick(U32, (a < b : U32), (b - a : U32), (a - b : U32))

def dist(+pos: U32, +v: U32) -> U32:
  +g = (v - 1 : U32)
  (absdiff((pos / 3 : U32), (g / 3 : U32)) + absdiff((pos % 3 : U32), (g % 3 : U32)) : U32)

# i: 列の位置, p: 空きマス。列の i 番目のタイルは盤面の i (i < p) か i+1 (i >= p) にある
def manhattan.go(l: List<&2, Nat>, +i: U32, +p: U32) -> U32:
  match l:
    case Nil{}:
      0
    case v <> t:
      (dist(pick(U32, (i < p : U32), i, (i + 1 : U32)), U32.from_nat(v)) + manhattan.go(t, (i + 1 : U32), p) : U32)

def manhattan(b: Board) -> U32:
  Board{p, ts} = b
  manhattan.go(ts, 0, U32.from_nat(p))

# 手の番号 (逆向きの手は番号の和が 3 になる)
def move_id(m: Move) -> Nat:
  match m:
    case Up{}:
      0n
    case Down{}:
      3n
    case Left{}:
      1n
    case Right{}:
      2n

def opposite(prev: Maybe<&2, Move>, m: Move) -> Bool:
  match prev:
    case None{}:
      False{}
    case Some{q}:
      nat_eq(Nat.add(move_id(q), move_id(m)), 3n)

def blank_of(b: Board) -> Nat:
  Board{p, ts} = b
  p

type Node is Data:
  Dead{}
  Goal{}
  Open{board: Board}

# 残り n 手以内でゴールに届く見込みがあるか
def classify(+b: Board, +n: Nat) -> Node:
  pick(Node, is_goal(b), Goal{}, pick(Node, (U32.from_nat(n) < manhattan(b) : U32), Dead{}, Open{b}))

# 空きマスから手 m を指した子ノード。盤外・直前の手の取り消しは Dead
def child(+b: Board, +m: Move, +prev: Maybe<&2, Move>, +n: Nat) -> Node:
  +c = step(m, b)
  same = nat_eq(blank_of(c), blank_of(b))
  pick(Node, same || opposite(prev, m), Dead{}, classify(c, n))

def found(m: Move, r: Maybe<&2, List<&2, Move>>) -> Maybe<&2, List<&2, Move>>:
  match r:
    case None{}:
      None{}
    case Some{ms}:
      Some{m <> ms}

def first(a: Maybe<&2, List<&2, Move>>, b: Maybe<&2, List<&2, Move>>) -> Maybe<&2, List<&2, Move>>:
  match a:
    case None{}:
      b
    case Some{x}:
      Some{x}

# n: 残りの深さ。4 方向は並列呼び出しで同時に探索する
def dfs(+n: Nat, node: Node, +prev: Maybe<&2, Move>) -> Maybe<&2, List<&2, Move>>:
  match n:
    case 0n:
      match node:
        case Goal{}:
          Some{Nil{}}
        case _:
          None{}
    case 1n+k:
      match node:
        case Dead{}:
          None{}
        case Goal{}:
          Some{Nil{}}
        case Open{+b}:
          r0 r1 = dfs(k, child(b, Up{}, prev, k), Some{Up{}}) dfs(k, child(b, Down{}, prev, k), Some{Down{}})
          r2 r3 = dfs(k, child(b, Left{}, prev, k), Some{Left{}}) dfs(k, child(b, Right{}, prev, k), Some{Right{}})
          first(found(Up{}, r0), first(found(Down{}, r1), first(found(Left{}, r2), found(Right{}, r3))))

# 深さ d, d+2, d+4, ... と広げる。見つかったら止まる
def deepen(tries: Nat, +d: Nat, +b: Board, r: Maybe<&2, List<&2, Move>>) -> Maybe<&2, List<&2, Move>>:
  match tries:
    case 0n:
      r
    case 1n+t:
      match r:
        case Some{ms}:
          Some{ms}
        case None{}:
          deepen(t, Nat.add(d, 2n), b, dfs(d, classify(b, d), None{}))

def solve(+b: Board) -> Maybe<&2, List<&2, Move>>:
  deepen(17n, U32.to_nat(manhattan(b)), b, None{})

# 表示
# ----

def show_move(m: Move) -> String:
  match m:
    case Up{}:
      "U"
    case Down{}:
      "D"
    case Left{}:
      "L"
    case Right{}:
      "R"

def show_moves(ms: List<&2, Move>) -> String:
  match ms:
    case Nil{}:
      ""
    case m <> t:
      show_move(m) ++ show_moves(t)

def length(ms: List<&2, Move>) -> Nat:
  match ms:
    case Nil{}:
      0n
    case m <> t:
      1n+length(t)

def lead(+i: Nat) -> String:
  pick(String, nat_eq(Nat.mod(i, 3n), 0n), "   ", "")

def eol(+i: Nat) -> String:
  pick(String, nat_eq(Nat.mod(i, 3n), 2n), "\n", "")

# 盤面の 9 マスを左上から描く
def cells(+n: Nat, +i: Nat, +p: Nat, +ts: List<&2, Nat>) -> String:
  match n ts:
    case 0n _:
      ""
    case 1n+k Nil{}:
      lead(i) ++ pick(String, nat_eq(i, p), " .", "") ++ eol(i) ++ cells(k, 1n+i, p, Nil{})
    case 1n+k Con{+v, +t}:
      lead(i) ++ pick(String, nat_eq(i, p), " ." ++ eol(i) ++ cells(k, 1n+i, p, v <> t), " " ++ Nat.show(v) ++ eol(i) ++ cells(k, 1n+i, p, t))

def show_board(b: Board) -> String:
  Board{p, ts} = b
  cells(9n, 0n, p, ts)

def verdict(+b: Board, r: Maybe<&2, List<&2, Move>>) -> String:
  match r:
    case None{}:
      "   => 偶数だが探索上限内で手順が見つからない\n"
    case Some{+ms}:
      ok = pick(String, is_goal(replay(b, ms)), "検証OK: 手順を再適用してゴールに到達", "検証NG")
      "   => 解ける。最短 " ++ Nat.show(length(ms)) ++ " 手: " ++ show_moves(ms) ++ "\n      " ++ ok ++ "\n"

# pick は両方の枝を計算してしまうので、ソルバーを呼ぶ分岐は match で書く
def judge(o: Bool, +b: Board) -> String:
  match o:
    case True{}:
      " (奇数)\n   => 解けない。LAWS.bend の odd_never_solved により証明済み\n"
    case False{}:
      " (偶数)\n" ++ verdict(b, solve(b))

def report(name: String, +b: Board) -> String:
  Board{+p, +ts} = b
  head = "== " ++ name ++ " ==\n" ++ show_board(Board{p, ts}) ++ "   転倒数 = " ++ Nat.show(inversions(ts))
  head ++ judge(odd(Board{p, ts}), Board{p, ts})

# 例題 (0 = 空きマス)
# ------------------

def easy() -> Board:
  from_grid([1n, 2n, 3n, 4n, 5n, 6n, 7n, 0n, 8n])

def medium() -> Board:
  from_grid([1n, 2n, 3n, 0n, 4n, 6n, 7n, 5n, 8n])

def odd_case() -> Board:
  from_grid([2n, 8n, 3n, 1n, 6n, 4n, 7n, 0n, 5n])

def hard() -> Board:
  from_grid([8n, 6n, 7n, 2n, 5n, 4n, 3n, 0n, 1n])

def swap78() -> Board:
  from_grid([1n, 2n, 3n, 4n, 5n, 6n, 8n, 7n, 0n])

def reversed() -> Board:
  from_grid([8n, 7n, 6n, 5n, 4n, 3n, 2n, 1n, 0n])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("8パズル 可解性プルーバー (Bend 2)\n")
    IO.print(report("ほぼ完成", easy()))
    IO.print(report("ちょっと崩した", medium()))
    IO.print(report("中級", odd_case()))
    IO.print(report("上級", hard()))
    IO.print(report("8と7を交換", swap78()))
    IO.print(report("逆順", reversed()))
