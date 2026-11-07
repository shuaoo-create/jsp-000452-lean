import OriginalDominatingSetCost
import ExactPathEvenSplit
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- If S dominates every original D-degree vertex, coloring all edges meeting
S blue precludes the complete red forest with first head D at the endpoint. -/
theorem dominating_set_pays_blue_suffix {s t r : ℕ} (G : SimpleGraph X) (D : ℕ) (positive : 0<D)
    (hs : 0<s) (n : Fin s→ℕ) (m : Fin t→ℕ) (pm : ∀j,1≤m j)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (head : n ⟨0,hs⟩=D) (active : r<t)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (S : Set X)
    (dom : ∀v,Nat.card (G.neighborSet v)=D → v∈S ∨ ∃w∈S,G.Adj v w) : t-r≤S.ncard := by
  classical
  let R : SimpleGraph X := {
    Adj := fun x y => G.Adj x y ∧ x∉S ∧ y∉S
    symm := ⟨fun _ _ e => ⟨e.1.symm,e.2.2,e.2.1⟩⟩
    loopless := ⟨fun _ e => G.irrefl e.1⟩ }
  have sub : R≤G := fun _ _ e => e.1
  have redSmall (v:X) : Nat.card (R.neighborSet v)<D := by
    by_cases removed : v∈S
    · have empty : R.neighborSet v=∅ := Set.eq_empty_iff_forall_notMem.mpr (fun w e => e.2.1 removed)
      rw [Nat.card_coe_set_eq,empty,Set.ncard_empty];exact positive
    have subset : R.neighborSet v⊆G.neighborSet v := fun _ e => e.1
    by_cases full : Nat.card (G.neighborSet v)=D
    · obtain ⟨w,ws,e⟩ := (dom v full).resolve_left removed
      have strict : R.neighborSet v ⊂ G.neighborSet v := ⟨subset,fun back => (back e).2.2 ws⟩
      exact (show Nat.card (R.neighborSet v)<Nat.card (G.neighborSet v) from Set.ncard_lt_ncard strict).trans_eq full
    · exact (show Nat.card (R.neighborSet v)≤Nat.card (G.neighborSet v) from Set.ncard_le_ncard subset).trans_lt
        (lt_of_le_of_ne (cap v) full)
  have blueCover : matchingEdges (G \ R)≤S.ncard := matchingEdges_le_cover_card _ S (by
    intro x y e
    by_cases xs:x∈S
    · exact Or.inl xs
    · exact Or.inr (Classical.byContradiction (fun ys => e.2 ⟨e.1,xs,ys⟩)))
  have force := row 0 r s (t-r) (by omega) (by omega) (by omega) hs (by omega)
  rcases force R sub with red|blue
  · have origin : (fun i : Fin s => padDemand n (0+i.val))=n := by funext i;simp [padDemand,i.isLt]
    change (forest (fun i : Fin s => padDemand n (0+i.val))).IsContained R at red
    rw [origin] at red
    obtain ⟨f⟩ := red
    obtain ⟨w⟩ := oneStar_in_forest n ⟨0,hs⟩
    let g := f.comp w
    have large := star_copy_center_degree R g
    have small := redSmall (g (center (fun _ : Fin 1 => n ⟨0,hs⟩) 0))
    omega
  · have bound := forest_copy_matching (G \ R) (fun j : Fin (t-r) => padDemand m (r+j.val))
      (fun j => pad_positive m pm _ (by have := j.isLt;omega)) blue
    rw [Fintype.card_fin] at bound;omega

/-- The actual forced blue length prices the same exterior excess and
root/exterior incidences used by the constructive dominating set. -/
theorem original_head_dominating_price {s t r : ℕ} (G : SimpleGraph X) (D : ℕ) (positive : 0<D)
    (K : DegreeRegion G D) (hs : 0<s) (n : Fin s→ℕ) (m : Fin t→ℕ) (pm : ∀j,1≤m j)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (head : n ⟨0,hs⟩=D) (active : r<t)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ((D:ℚ)-1)*((t-r:ℕ):ℚ) ≤ ((D:ℚ)-1)*(1/4+(3/4:ℚ)^(D+1))*
        ((2*(K.roots.ncard+matchingEdges (G.induce K.core))+minimumExposure G D:ℕ):ℚ)+
        (((G.induce K.rest).edgeSet.ncard-matchingEdges (G.induce K.rest):ℕ):ℚ)+
        (crossCount G K.roots K.rest:ℚ) := by
  obtain ⟨S,dom,fee⟩ := ordinary_full_degree_dominating_set G positive K
  have bound := dominating_set_pays_blue_suffix G D positive hs n m pm cap head active row S dom
  have cast : ((t-r:ℕ):ℚ)≤S.ncard := by exact_mod_cast bound
  have scale : 0≤(D:ℚ)-1 := by apply sub_nonneg.mpr;exact_mod_cast (show 1≤D from positive)
  exact (mul_le_mul_of_nonneg_left cast scale).trans fee

#print axioms dominating_set_pays_blue_suffix
#print axioms original_head_dominating_price
end JSP452Audit.StarHost
