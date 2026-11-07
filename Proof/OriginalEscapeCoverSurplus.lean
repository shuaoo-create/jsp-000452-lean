import ComponentCoverLabels
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type*} [Finite X]

/-- Full-degree uncovered labels with no core neighbor can be charged to
covered roots, by counting their actual original incidences in both directions. -/
theorem free_labels_paid_at_roots (G : SimpleGraph X) {D : ℕ} (K : DegreeRegion G D)
    (pos : 0<D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (C : Set X) (cover : G.IsVertexCover C) :
    (freeCoreLabels G K.core C).ncard ≤ (K.roots∩C).ncard := by
  classical
  let U := freeCoreLabels G K.core C
  let A := K.roots∩C
  let _ := Fintype.ofFinite ↥U
  let _ := Fintype.ofFinite ↥A
  have nbr (x : U) : G.neighborSet x.val ⊆ A := by
    intro y e
    have around := regionCore_neighbor G K.barrier K.pieces x.property.1 e
    exact ⟨around.resolve_right (fun hy => x.property.2.2 y hy e),(cover e).resolve_left x.property.2.1⟩
  have ucard : Fintype.card ↥U=U.ncard := (Nat.card_eq_fintype_card (α:=↥U)).symm
  have acard : Fintype.card ↥A=A.ncard := (Nat.card_eq_fintype_card (α:=↥A)).symm
  have lo : crossCount G U A = D*U.ncard := by
    rw [crossCount_eq_neighbor_sum]
    calc
      _ = ∑ _x : U, D := Finset.sum_congr rfl (fun x _ => by
        rw [Set.inter_eq_left.mpr (nbr x)]
        exact regionCore_full_degree G K.barrier K.pieces D K.full x.property.1)
      _ = _ := by simp [ucard,Nat.mul_comm]
  have hi : crossCount G A U ≤ D*A.ncard := by
    rw [crossCount_eq_neighbor_sum]
    calc
      _ ≤ ∑ _x : A, D := Finset.sum_le_sum (fun x _ =>
        (Set.ncard_le_ncard (Set.inter_subset_left : G.neighborSet x.val∩U⊆G.neighborSet x.val)).trans (cap x.val))
      _ = _ := by simp [acard,Nat.mul_comm]
  rw [←crossCount_swap G U A,lo] at hi
  exact Nat.le_of_mul_le_mul_left hi pos

theorem core_cover_and_roots (G : SimpleGraph X) {D : ℕ} (K : DegreeRegion G D)
    (pos : 0<D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (C : Set X) (cover : G.IsVertexCover C) :
    matchingEdges (G.induce K.core)+K.roots.ncard+minimumExposure G D ≤ (K.core∩C).ncard+(K.roots∩C).ncard := by
  classical
  let _ := Fintype.ofFinite ↥K.pieces
  let U := freeCoreLabels G K.core C
  have sum := Finset.sum_le_sum (s := (Finset.univ : Finset K.pieces)) (fun c _ => component_cover_account G K C cover c)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_one,←Finset.mul_sum] at sum
  rw [←core_order_sum,←selected_label_count,←selected_label_count] at sum
  change K.core.ncard+Fintype.card K.pieces≤2*(K.core∩C).ncard+2*(K.core∩U).ncard at sum
  have sub : U⊆K.core := fun _ h => h.1
  rw [Set.inter_eq_right.mpr sub] at sum
  have count := core_order_matching G K.barrier K.tight K.pieces (fun c _ => (K.critical c).1)
  change K.core.ncard=2*matchingEdges (G.induce K.core)+K.pieces.ncard at count
  have ids : Fintype.card ↥K.pieces=K.pieces.ncard := (Nat.card_eq_fintype_card (α:=↥K.pieces)).symm
  have order := K.core_order
  have charge := free_labels_paid_at_roots G K pos cap C cover
  change U.ncard≤(K.roots∩C).ncard at charge
  omega

/-- In every possible escaping region, the actual source cover has
at least the original rank plus the original peak exposure. -/
theorem strict_escape_original_cover (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (C : Set F.X) (cover : F.G.IsVertexCover C) :
    F.rank+minimumExposure F.G (diagonal F.n F.m (F.r+2)-1)≤C.ncard := by
  let D := diagonal F.n F.m (F.r+2)-1
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have d3 : 3≤D := strict_source_degree_at_least_three F paid
  have core := core_cover_and_roots F.G K (by change 0<D;omega) cap C cover
  have rest := strict_escape_exterior_cover F paid K C cover
  have split := region_rank_partition F.G K.barrier K.tight K.pieces
  change matchingEdges F.G=K.roots.ncard+matchingEdges (F.G.induce K.core)+matchingEdges (F.G.induce K.rest) at split
  obtain ⟨ac,ab,cb,_⟩ := region_partition F.G K.barrier K.pieces
  have ac' : Disjoint (K.roots∩C) (K.core∩C) := ac.mono Set.inter_subset_left Set.inter_subset_left
  have ab' : Disjoint (K.roots∩C) (K.rest∩C) := ab.mono Set.inter_subset_left Set.inter_subset_left
  have cb' : Disjoint (K.core∩C) (K.rest∩C) := cb.mono Set.inter_subset_left Set.inter_subset_left
  have size := Set.ncard_le_ncard (show (K.roots∩C)∪(K.core∩C)∪(K.rest∩C)⊆C from
    Set.union_subset (Set.union_subset Set.inter_subset_right Set.inter_subset_right) Set.inter_subset_right)
  rw [Set.ncard_union_eq (Disjoint.union_left ab' cb'),Set.ncard_union_eq ac'] at size
  omega

#print axioms free_labels_paid_at_roots
#print axioms core_cover_and_roots
#print axioms strict_escape_original_cover
end JSP452Audit.StarHost
