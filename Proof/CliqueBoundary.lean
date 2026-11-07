import PartitionHandshake
import RegionDegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Inside a clique each vertex has every other clique vertex as a neighbor. -/
theorem clique_external_degree (G : SimpleGraph X) (C : Set X) (D : ℕ)
    (cl : G.IsClique C) (full : ∀ x ∈ C, Nat.card (G.neighborSet x) = D) (x : C) :
    (G.neighborSet x.val ∩ Cᶜ).ncard = D+1-C.ncard := by
  have inside : G.neighborSet x.val ∩ C = C \ {x.val} := by
    ext y
    constructor
    · intro h
      exact ⟨h.2,fun eq => h.1.ne (Set.mem_singleton_iff.mp eq).symm⟩
    · intro h
      exact ⟨cl x.property h.1 (fun eq => h.2 (Set.mem_singleton_iff.mpr eq.symm)),h.1⟩
  have total := Set.ncard_sdiff_add_ncard_of_subset (s := G.neighborSet x.val ∩ C)
    (t := G.neighborSet x.val) Set.inter_subset_left
  have external : G.neighborSet x.val \ (G.neighborSet x.val ∩ C) = G.neighborSet x.val ∩ Cᶜ := by
    ext y; simp only [Set.mem_sdiff,Set.mem_inter_iff,Set.mem_compl_iff]; tauto
  rw [external,inside, Set.ncard_sdiff' (Set.singleton_subset_iff.mpr x.property),
    Set.ncard_singleton, show (G.neighborSet x.val).ncard = D from full x.val x.property] at total
  have pos := (Set.ncard_pos (s := C)).mpr ⟨x.val,x.property⟩
  omega

theorem clique_boundary_count (G : SimpleGraph X) (C : Set X) (D : ℕ)
    (cl : G.IsClique C) (full : ∀ x ∈ C, Nat.card (G.neighborSet x) = D) :
    crossCount G C Cᶜ = C.ncard * (D+1-C.ncard) := by
  classical
  let _ := Fintype.ofFinite C
  rw [crossCount_eq_neighbor_sum]
  simp only [clique_external_degree G C D cl full,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]

theorem clique_boundary_at_least_degree (G : SimpleGraph X) (C : Set X) (D : ℕ)
    (cl : G.IsClique C) (full : ∀ x ∈ C, Nat.card (G.neighborSet x) = D)
    (positive : 1 ≤ C.ncard) (small : C.ncard ≤ D) :
    D ≤ crossCount G C Cᶜ := by
  rw [clique_boundary_count G C D cl full]
  have gap : D = C.ncard + (D-C.ncard) := by omega
  have delta : D+1-C.ncard = 1+(D-C.ncard) := by omega
  have bound := Nat.mul_le_mul_right (D-C.ncard) positive
  rw [delta,Nat.mul_add,Nat.mul_one]
  omega

/-- Distinct disjoint cliques use disjoint neighbor labels at each root.
Bounding the root degrees pays at most one qualifying clique per root. -/
theorem clique_family_le_roots {I : Type*} [Fintype I] (G : SimpleGraph X)
    (C : I → Set X) (roots : Set X) (D : ℕ) (posD : 0<D)
    (pairwise : ∀ i j, i≠j → Disjoint (C i) (C j))
    (cl : ∀ i, G.IsClique (C i)) (full : ∀ i x, x∈C i → Nat.card (G.neighborSet x)=D)
    (pos : ∀ i, 1≤(C i).ncard) (small : ∀ i,(C i).ncard≤D)
    (external : ∀ i x, x∈C i → ∀ y, G.Adj x y → y∉C i → y∈roots)
    (rootCap : ∀ x∈roots, Nat.card (G.neighborSet x)≤D) : Nat.card I ≤ roots.ncard := by
  classical
  let _ := Fintype.ofFinite roots
  have cost (i : I) : D ≤ crossCount G roots (C i) := by
    let _ := Fintype.ofFinite (C i)
    have le := clique_boundary_at_least_degree G (C i) D (cl i) (full i) (pos i) (small i)
    rw [crossCount_swap G roots (C i),crossCount_eq_neighbor_sum G (C i) roots]
    rw [crossCount_eq_neighbor_sum] at le
    exact le.trans (Finset.sum_le_sum (fun x _ => Set.ncard_le_ncard
      (fun _ h => ⟨h.1,external i x.val x.property _ h.1 h.2⟩)))
  have budget (x : roots) : (∑ i, (G.neighborSet x.val ∩ C i).ncard) ≤ D := by
    let f (p : (i : I) × ↥(G.neighborSet x.val ∩ C i)) : G.neighborSet x.val := ⟨p.2.val,p.2.property.1⟩
    have inj : Function.Injective f := by
      rintro ⟨i,a⟩ ⟨j,b⟩ eq
      have labels : a.val = b.val := congrArg Subtype.val eq
      have indices : i=j := by
        by_contra diff
        exact Set.disjoint_left.mp (pairwise i j diff) a.property.2 (labels ▸ b.property.2)
      subst j
      exact congrArg (Sigma.mk i) (Subtype.ext labels)
    have le := Nat.card_le_card_of_injective f inj
    rw [Nat.card_sigma] at le
    exact le.trans (rootCap x.val x.property)
  have total : Nat.card I*D ≤ roots.ncard*D := calc
    Nat.card I*D = ∑ _ : I, D := by simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ i, crossCount G roots (C i) := Finset.sum_le_sum (fun i _ => cost i)
    _ = ∑ x : roots, ∑ i, (G.neighborSet x.val ∩ C i).ncard := by
      simp only [crossCount_eq_neighbor_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ _ : roots, D := Finset.sum_le_sum (fun x _ => budget x)
    _ = roots.ncard*D := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  exact Nat.le_of_mul_le_mul_right total posD

#print axioms clique_boundary_count
#print axioms clique_boundary_at_least_degree
#print axioms clique_family_le_roots
end JSP452Audit.StarHost
