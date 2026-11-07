import CliqueBoundary
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X I : Type*} [Finite X] [Fintype I]

/-- Every boundary edge of these disjoint regions ends in the same roots.
Count their incident neighbors once at each root. -/
theorem disjoint_cut_total_budget (G : SimpleGraph X) (C : I→Set X) (roots : Set X) (D : ℕ)
    (apart : ∀i j,i≠j → Disjoint (C i) (C j))
    (external : ∀i x,x∈C i → ∀y,G.Adj x y → y∉C i → y∈roots)
    (rootCap : ∀x∈roots,Nat.card (G.neighborSet x)≤D) :
    (∑i,crossCount G (C i) (C i)ᶜ) ≤ roots.ncard*D := by
  classical
  let _ := Fintype.ofFinite roots
  have each (i : I) : crossCount G (C i) (C i)ᶜ ≤ crossCount G roots (C i) := by
    let _ := Fintype.ofFinite (C i)
    rw [crossCount_swap G roots (C i),crossCount_eq_neighbor_sum,crossCount_eq_neighbor_sum]
    exact Finset.sum_le_sum (fun x _ => Set.ncard_le_ncard
      (fun _ h => ⟨h.1,external i x.val x.property _ h.1 h.2⟩))
  have bound (x : roots) : (∑ i,(G.neighborSet x.val ∩ C i).ncard)≤D := by
    let S (i : I) := G.neighborSet x.val ∩ C i
    have dis : Pairwise (Function.onFun Disjoint S) := by
      intro i j ne
      exact (apart i j ne).mono Set.inter_subset_right Set.inter_subset_right
    have sub : (⋃i,S i)⊆G.neighborSet x.val := by
      intro y h
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
      exact hi.1
    have le := Set.ncard_le_ncard sub
    rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite (S i)) dis,finsum_eq_sum_of_fintype] at le
    exact le.trans (rootCap x.val x.property)
  calc
    _ ≤ ∑ i,crossCount G roots (C i) := Finset.sum_le_sum (fun i _ => each i)
    _ = ∑ x : roots,∑ i,(G.neighborSet x.val ∩ C i).ncard := by
      simp only [crossCount_eq_neighbor_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ _ : roots,D := Finset.sum_le_sum (fun x _ => bound x)
    _ = _ := by simp [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]

/-- Equality in the family count forces every clique to have size 1 or D.
Any intermediate clique has an extra boundary-edge cost. -/
theorem tight_clique_family_sizes (G : SimpleGraph X) (C : I→Set X) (roots : Set X) (D : ℕ)
    (same : Nat.card I=roots.ncard)
    (apart : ∀i j,i≠j → Disjoint (C i) (C j))
    (cl : ∀i,G.IsClique (C i)) (full : ∀i x,x∈C i → Nat.card (G.neighborSet x)=D)
    (pos : ∀i,1≤(C i).ncard) (small : ∀i,(C i).ncard≤D)
    (external : ∀i x,x∈C i → ∀y,G.Adj x y → y∉C i → y∈roots)
    (rootCap : ∀x∈roots,Nat.card (G.neighborSet x)≤D) :
    ∀i,(C i).ncard=1 ∨ (C i).ncard=D := by
  classical
  have budget := disjoint_cut_total_budget G C roots D apart external rootCap
  have cost (i) := clique_boundary_at_least_degree G (C i) D (cl i) (full i) (pos i) (small i)
  intro i
  by_contra! neither
  let k := (C i).ncard
  have one : 1<k := by have h:=pos i;dsimp [k];omega
  have top : k<D := by have h:=small i;dsimp [k];omega
  have above : D<crossCount G (C i) (C i)ᶜ := by
    rw [clique_boundary_count G (C i) D (cl i) (full i)]
    change D<k*(D+1-k)
    have delta : D+1-k=1+(D-k) := by omega
    have spend := Nat.mul_lt_mul_of_pos_right one (show 0<D-k by omega)
    rw [delta,Nat.mul_add,Nat.mul_one]
    omega
  have overspend := Finset.sum_lt_sum (fun j _ => cost j) ⟨i,Finset.mem_univ _,above⟩
  have total : (∑ _ : I,D)=roots.ncard*D := by simp [←Nat.card_eq_fintype_card,same]
  omega

#print axioms tight_clique_family_sizes
end JSP452Audit.StarHost
