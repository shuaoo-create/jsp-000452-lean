import RegionWeights
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Count genuine oriented adjacencies one origin at a time. -/
theorem crossCount_eq_neighbor_sum (G : SimpleGraph X) (U V : Set X) [Fintype U] :
    crossCount G U V = ∑ x : U, (G.neighborSet x.val ∩ V).ncard := by
  let e : {p : (↥U × ↥V) // G.Adj p.1.val p.2.val} ≃
      ((x : U) × ↥(G.neighborSet x.val ∩ V)) := {
    toFun := fun p => ⟨p.val.1,⟨p.val.2.val,p.property,p.val.2.property⟩⟩
    invFun := fun p => ⟨(p.1,⟨p.2.val,p.2.property.2⟩),p.2.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans Nat.card_sigma

/-- The two labels of each undirected internal edge contribute one dart each. -/
theorem crossCount_self (G : SimpleGraph X) (U : Set X) :
    crossCount G U U = 2 * (G.induce U).edgeSet.ncard := by
  classical
  let _ := Fintype.ofFinite U
  let H := G.induce U
  let e : {p : (↥U × ↥U) // G.Adj p.1.val p.2.val} ≃ H.Dart := {
    toFun := fun p => ⟨p.val,p.property⟩
    invFun := fun d => ⟨d.toProd,d.adj⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    crossCount G U U = Nat.card H.Dart := Nat.card_congr e
    _ = 2 * H.edgeSet.ncard := by
      rw [Nat.card_eq_fintype_card,H.dart_card_eq_twice_card_edges,← Nat.card_coe_set_eq,
        Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet]

/-- For a three-block partition, original degrees over U count the internal
edges twice and each edge from U to either other block once. -/
theorem partition_handshake (G : SimpleGraph X) (U V W : Set X)
    (uv : Disjoint U V) (uw : Disjoint U W) (vw : Disjoint V W) (cover : U ∪ V ∪ W = Set.univ) :
    originalDegreeSum G U = 2 * (G.induce U).edgeSet.ncard + crossCount G U V + crossCount G U W := by
  classical
  let _ := Fintype.ofFinite U
  have total : originalDegreeSum G U = ∑ x : U, (G.neighborSet x.val).ncard :=
    Finset.sum_subtype U.toFinite.toFinset (fun _ => U.toFinite.mem_toFinset) (fun x => (G.neighborSet x).ncard)
  have point (x : U) :
      (G.neighborSet x.val).ncard =
        (G.neighborSet x.val ∩ U).ncard + (G.neighborSet x.val ∩ V).ncard +
          (G.neighborSet x.val ∩ W).ncard := by
    let N := G.neighborSet x.val
    have split : N ∩ U ∪ N ∩ V ∪ N ∩ W = N := by
      rw [← Set.inter_union_distrib_left,← Set.inter_union_distrib_left,cover,Set.inter_univ]
    have d1 : Disjoint (N ∩ U) (N ∩ V) := uv.mono Set.inter_subset_right Set.inter_subset_right
    have d2 : Disjoint (N ∩ U ∪ N ∩ V) (N ∩ W) := by
      apply Set.disjoint_left.mpr
      rintro y (yu | yv) yw
      · exact Set.disjoint_left.mp uw yu.2 yw.2
      · exact Set.disjoint_left.mp vw yv.2 yw.2
    have h := congrArg Set.ncard split
    rw [Set.ncard_union_eq d2,Set.ncard_union_eq d1] at h
    exact h.symm
  rw [total,← crossCount_self G U,crossCount_eq_neighbor_sum G U U,
    crossCount_eq_neighbor_sum G U V,crossCount_eq_neighbor_sum G U W]
  simpa only [Finset.sum_add_distrib] using Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => point x)

#print axioms crossCount_eq_neighbor_sum
#print axioms crossCount_self
#print axioms partition_handshake
end JSP452Audit.StarHost
