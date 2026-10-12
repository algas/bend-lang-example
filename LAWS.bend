# 8パズルの法則。人間が主張を書き、PROOF.bend がそれを証明する。
# `bend PROOF.bend` が ALL PROOFS CHECK を出せば、すべて数学的に正しい。

import Base
import ./main.bend as Pz

# 法則1: 不変量
# 「タイルが全部異なり、転倒数が奇数」かどうか (odd) は、
# どんな盤面からどんな手順を指しても変わらない。
law parity_invariant:
  for +b: Pz.Board
  for +moves: List<&2, Pz.Move>
  {Pz.odd(Pz.replay(b, moves)) == Pz.odd(b) : Bool}

# 法則2: 解けないことの一般証明
# odd な盤面からは、どんな手順を指してもゴールに着かない。
law odd_never_solved:
  for +b: Pz.Board
  for e: {Pz.odd(b) == True{} : Bool}
  for +moves: List<&2, Pz.Move>
  {Pz.is_goal(Pz.replay(b, moves)) == False{} : Bool}

# 法則3: 「8と7を交換」は解けない
law swap78_unsolvable:
  for moves: List<&2, Pz.Move>
  {Pz.is_goal(Pz.replay(Pz.swap78(), moves)) == False{} : Bool}

# 法則4: 「中級」も解けない
law odd_case_unsolvable:
  for moves: List<&2, Pz.Move>
  {Pz.is_goal(Pz.replay(Pz.odd_case(), moves)) == False{} : Bool}

# 法則5: 「上級」は解ける (ゴールに着く手順が存在する)
law hard_solvable:
  exs moves: List<&2, Pz.Move>
  {Pz.is_goal(Pz.replay(Pz.hard(), moves)) == True{} : Bool}

# 法則6: 「逆順」も解ける
law reversed_solvable:
  exs moves: List<&2, Pz.Move>
  {Pz.is_goal(Pz.replay(Pz.reversed(), moves)) == True{} : Bool}
