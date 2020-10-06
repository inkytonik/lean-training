import tactic

set_option pp.generalized_field_notation false

open nat

namespace training

def powerOf2 : ℕ → ℕ
| 0     := 1
| (n+1) := 2 * powerOf2 n

lemma lowerBoundPowerOf2 (n : ℕ) :
  1 ≤ powerOf2 n :=
begin
  induction n; simp [powerOf2], linarith,
end

lemma sumSamePowerOf2 (n : ℕ) :
  powerOf2 n + powerOf2 n == 2 * powerOf2 n :=
by ring

lemma monotonicPowerOf2 :
  ∀ {n m}, n ≤ m → powerOf2 n ≤ powerOf2 m
| 0     m     le := lowerBoundPowerOf2 m
| (n+1) 0     le := by cases le
| (n+1) (m+1) le := begin simp [powerOf2], apply monotonicPowerOf2, linarith, end

lemma addPowerOf2 (n m : ℕ) :
  powerOf2 n * powerOf2 m = powerOf2 (n + m) :=
begin
  induction n; simp [powerOf2], rw [mul_assoc, n_ih, succ_add], ring,
end

inductive tree : Type
| leaf : tree
| node : tree → tree → tree

namespace tree

def height : tree → ℕ
| leaf       := 1
| (node l r) := max (height l) (height r) + 1

def nodeCount : tree → ℕ
| leaf       := 1
| (node l r) := nodeCount l + nodeCount r + 1

def leafCount : tree → ℕ
| leaf       := 1
| (node l r) := leafCount l + leafCount r

-- Move - 1 to LHS to avoid nat subtraction

lemma upperboundForNodeCount (root : tree) :
  nodeCount root + 1 ≤ powerOf2 (height root) :=
begin
  induction root with l r ih_l ih_r;
  simp [height, nodeCount, powerOf2],
  set hl := height l,
  set hr := height r,
  calc
    nodeCount (node l r) + 1
        = nodeCount l + nodeCount r + 1 + 1            : rfl
    ... ≤ powerOf2 hl + powerOf2 hr                    : by linarith
    ... ≤ powerOf2 (max hl hr) + powerOf2 (max hl hr)  :
      by linarith [ monotonicPowerOf2 (le_max_left hl hr)
                  , monotonicPowerOf2 (le_max_right hl hr) ]
    ... = 2 * powerOf2 (max hl hr)                     : by ring
    ... = powerOf2 (max hl hr + 1)                     : rfl
    ... = powerOf2 (height (node l r))                 : rfl
end

end tree

end training
