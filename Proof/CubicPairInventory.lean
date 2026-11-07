import CubicLabelledRankBound
import OrientDifference
namespace JSP452Audit.StarHost
open SimpleGraph
namespace CubicPairFamily
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]

theorem degree_univ_fibers (P:CubicPairFamily X I) (x:X) :
    P.degree Set.univ x=Nat.card {i:I // P.left i=x}+Nat.card {i:I // P.right i=x} := by
  classical
  have full : P.active Set.univ=Finset.univ := by ext i;simp [mem_active]
  unfold degree;rw [full]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]

private theorem filtered_fiber_card (A:Finset I) (fn:I→X) (x:X) [DecidableEq X] :
    (A.filter (fun i => fn i=x)).card=Nat.card {i:↥A // fn i.val=x} := by
  let e : ↥(A.filter (fun i => fn i=x)) ≃ {i:↥A // fn i.val=x} := {
    toFun := fun t => ⟨⟨t.val,(Finset.mem_filter.mp t.property).1⟩,(Finset.mem_filter.mp t.property).2⟩
    invFun := fun t => ⟨t.val.val,Finset.mem_filter.mpr ⟨t.val.property,t.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_congr e

def inside (P:CubicPairFamily X I) (U:Set X) : CubicPairFamily ↥U ↥(P.active U) where
  left i := ⟨P.left i.val,((P.mem_active U i.val).1 i.property).1⟩
  right i := ⟨P.right i.val,((P.mem_active U i.val).1 i.property).2⟩
  distinct i eq := P.distinct i.val (congrArg Subtype.val eq)

theorem inside_degree (P:CubicPairFamily X I) (U:Set X) [Fintype U] (x:U) :
    (P.inside U).degree Set.univ x=P.degree U x.val := by
  classical
  rw [degree_univ_fibers]
  unfold degree
  rw [filtered_fiber_card (P.active U) P.left x.val,filtered_fiber_card (P.active U) P.right x.val]
  congr 1
  · apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun i => Subtype.ext_iff)
  · apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun i => Subtype.ext_iff)

def combine (A:CubicPairFamily X I) (B:CubicPairFamily X J) : CubicPairFamily X (I⊕J) where
  left := Sum.elim A.left B.left
  right := Sum.elim A.right B.right
  distinct i := by cases i with
                   | inl j => exact A.distinct j
                   | inr j => exact B.distinct j

theorem combine_degree (A:CubicPairFamily X I) (B:CubicPairFamily X J) (x:X) :
    (A.combine B).degree Set.univ x=A.degree Set.univ x+B.degree Set.univ x := by
  rw [degree_univ_fibers,degree_univ_fibers,degree_univ_fibers]
  have split (f:I→X) (g:J→X) : Nat.card {i:I⊕J // Sum.elim f g i=x}=
      Nat.card {i:I // f i=x}+Nat.card {j:J // g j=x} := by
    simpa only [Nat.card_sum,Sum.elim_inl,Sum.elim_inr] using Nat.card_congr (Equiv.subtypeSum (p:=fun i => Sum.elim f g i=x))
  change Nat.card {i:I⊕J // Sum.elim A.left B.left i=x}+Nat.card {i:I⊕J // Sum.elim A.right B.right i=x}=_
  rw [split,split]
  omega

noncomputable def ofGraph (G : SimpleGraph X) : CubicPairFamily X G.edgeSet where
  left e := graphEnds G e false
  right e := graphEnds G e true
  distinct e := (show G.Adj (graphEnds G e false) (graphEnds G e true) by
    change s(graphEnds G e false,graphEnds G e true)∈G.edgeSet;rw [graphEnds_edge G e];exact e.property).ne

theorem graph_pair_degree (G : SimpleGraph X) [Fintype G.edgeSet] (x:X) :
    (ofGraph G).degree Set.univ x=Nat.card (G.neighborSet x) := by
  rw [degree_univ_fibers]
  have counts := orientation_incident_count (graphEnds G) (fun _ => false) x
  rw [graphEnds_incidence_count] at counts
  exact counts

end CubicPairFamily
#print axioms CubicPairFamily.inside_degree
#print axioms CubicPairFamily.combine_degree
#print axioms CubicPairFamily.graph_pair_degree
end JSP452Audit.StarHost
