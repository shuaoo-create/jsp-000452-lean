import DeletionBudget
import PathCycleMatching

namespace JSP452Audit.StarHost
open SimpleGraph

/-- When every vertex has at most one neighbor, take all edges, on their
actual support, as a matching. Its relative edge complement is empty. -/
theorem admits_one_of_unique_neighbor {X : Type*} (G : SimpleGraph X)
    (unique : ∀ {v x y}, G.Adj v x → G.Adj v y → x = y) : admits_matching_remainder G 1 := by
  let M : G.Subgraph := {
    verts := G.support
    Adj := G.Adj
    adj_sub := fun h => h
    edge_vert := fun h => ⟨_,h⟩
    symm := ⟨fun _ _ h => h.symm⟩ }
  have matching : M.IsMatching := by
    intro x hx
    obtain ⟨y,hy⟩ := hx
    exact ⟨y,hy,fun z hz => unique hz hy⟩
  have empty : G \ M.spanningCoe = ⊥ := by
    ext v w
    exact ⟨fun h => h.2 h.1,False.elim⟩
  exact ⟨M,matching,fun v => by simp [empty]⟩

private theorem residue_cut_count {n r k : ℕ}
    (fits : ∀ v : Fin n, v.val % 3 = r → v.val / 3 < k) :
    ({v : Fin n | v.val % 3 = r} : Set (Fin n)).ncard ≤ k := by
  let S := {v : Fin n | v.val % 3 = r}
  let f (v : S) : Fin k := ⟨v.val.val/3,fits v.val v.property⟩
  have inject : Function.Injective f := by
    intro a b eq
    have h : a.val.val / 3 = b.val.val / 3 := congrArg Fin.val eq
    have ar : a.val.val % 3 = r := a.property
    have br : b.val.val % 3 = r := b.property
    exact Subtype.ext (Fin.ext (by omega))
  have le := Nat.card_le_card_of_injective f inject
  rw [Nat.card_fin] at le
  exact le

/-- Delete the original path labels 2,5,8,... . Every remaining vertex
belongs to an isolated point or an isolated edge. -/
theorem path_deletionBudget_one (n : ℕ) : deletionBudget (pathGraph n) 1 ≤ n / 3 := by
  let S : Set (Fin n) := {v | v.val % 3 = 2}
  have count : S.ncard ≤ n/3 := residue_cut_count (fun v mod => by have := v.isLt; omega)
  apply (deletionBudget_le_of_witness (pathGraph n) 1 S ?_).trans count
  apply admits_one_of_unique_neighbor
  intro x y z xy xz
  have xmod : x.val.val % 3 ≠ 2 := x.property
  have ymod : y.val.val % 3 ≠ 2 := y.property
  have zmod : z.val.val % 3 ≠ 2 := z.property
  have pathXY : (pathGraph n).Adj x.val y.val := xy
  have pathXZ : (pathGraph n).Adj x.val z.val := xz
  rcases pathGraph_adj.mp pathXY with a | a <;> rcases pathGraph_adj.mp pathXZ with b | b <;>
    exact Subtype.ext (Fin.ext (by omega))

/-- A cycle edge avoiding label zero is an ordinary non-wrapping path edge. -/
private theorem cycle_adj_away_zero {n : ℕ} {v w : Fin n} (hv : 0 < v.val) (hw : 0 < w.val)
    (edge : (cycleGraph n).Adj v w) : (pathGraph n).Adj v w := by
  have direct {a b : Fin n} (apos : 0 < a.val) (step : (a-b).val = 1) : b.val+1=a.val := by
    by_cases le : b ≤ a
    · rw [Fin.sub_val_of_le le] at step
      omega
    · have lt : a.val < b.val := Nat.lt_of_not_ge le
      rw [Fin.val_sub,Nat.mod_eq_of_lt (by have := b.isLt; omega)] at step
      have := b.isLt
      omega
  rcases cycleGraph_adj'.mp edge with e | e
  · exact pathGraph_adj.mpr (Or.inr (direct hv e))
  · exact pathGraph_adj.mpr (Or.inl (direct hw e))

/-- Delete cycle labels 0,3,6,... . Removing 0 eliminates the wrap edge;
the possibly short last segment has at most two vertices. -/
theorem cycle_deletionBudget_one (n : ℕ) (_hn : 3 ≤ n) :
    deletionBudget (cycleGraph n) 1 ≤ (n+2)/3 := by
  let S : Set (Fin n) := {v | v.val % 3 = 0}
  have count : S.ncard ≤ (n+2)/3 := residue_cut_count (fun v mod => by have := v.isLt; omega)
  apply (deletionBudget_le_of_witness (cycleGraph n) 1 S ?_).trans count
  apply admits_one_of_unique_neighbor
  intro x y z xy xz
  have xmod : x.val.val % 3 ≠ 0 := x.property
  have ymod : y.val.val % 3 ≠ 0 := y.property
  have zmod : z.val.val % 3 ≠ 0 := z.property
  have pathXY := cycle_adj_away_zero (v := x.val) (w := y.val) (by omega) (by omega) xy
  have pathXZ := cycle_adj_away_zero (v := x.val) (w := z.val) (by omega) (by omega) xz
  rcases pathGraph_adj.mp pathXY with a | a <;> rcases pathGraph_adj.mp pathXZ with b | b <;>
    exact Subtype.ext (Fin.ext (by omega))

#print axioms path_deletionBudget_one
#print axioms cycle_deletionBudget_one
end JSP452Audit.StarHost
