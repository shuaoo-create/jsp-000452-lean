import QuarterSampleTransversal
import LargestIndependentLabels
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem choose_full_exterior_independent (G : SimpleGraph X) (B : Set X) (D : ℕ) :
    ∃S:Set X,S⊆B ∧ (∀v∈S,Nat.card (G.neighborSet v)=D) ∧ G.IsIndepSet S ∧
      ∀v∈B,Nat.card (G.neighborSet v)=D → v∈S ∨ ∃s∈S,G.Adj v s := by
  let T := {v | v∈B ∧ Nat.card (G.neighborSet v)=D}
  obtain ⟨I,ind,largest⟩ := exists_largest_independent_set (G.induce T)
  refine ⟨Subtype.val '' I,?_,?_,?_,?_⟩
  · rintro _ ⟨v,_,rfl⟩;exact v.property.1
  · rintro _ ⟨v,_,rfl⟩;exact v.property.2
  · rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne edge
    exact ind hv hw (fun eq => ne (congrArg Subtype.val eq)) edge
  · intro v vb degree
    let u : T := ⟨v,vb,degree⟩
    by_cases yes : u∈I
    · exact Or.inl ⟨u,yes,rfl⟩
    obtain ⟨w,hw,e⟩ := largest_independent_dominates (G.induce T) I ind largest u yes
    exact Or.inr ⟨w.val,⟨w,hw,rfl⟩,e⟩

private theorem independent_degree_cost (H : SimpleGraph X) (T : Set X) (ind : H.IsIndepSet T) :
    originalDegreeSum H T≤H.edgeSet.ncard-matchingEdges H+T.ncard := by
  have empty : H.induce T=⊥ := by
    ext x y;exact ⟨fun e => ind x.property y.property (show H.Adj x.val y.val from e).ne e,False.elim⟩
  have fee := root_deletion_cost H T
  rw [empty,SimpleGraph.edgeSet_bot,Set.ncard_empty,Nat.add_zero] at fee
  have rank := matching_rank_le_cut_add H T
  have low := matchingEdges_le_edgeCount (H.induce Tᶜ)
  have top := matchingEdges_le_edgeCount H
  omega

def labelImageEquiv (B S : Set X) (inc : S⊆B) : S ≃ ↥({v:B | v.val∈S} : Set B) where
  toFun v := ⟨⟨v.val,inc v.property⟩,v.property⟩
  invFun v := ⟨v.val.val,v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full exterior labels in an independent set cost (D−1) each, charged
only to e(B)−ν(B) and their own edges to the original roots. -/
theorem exterior_independent_degree_price (G : SimpleGraph X) (B A S : Set X)
    (dis : Disjoint B A) (inc : S⊆B) (ind : G.IsIndepSet S) (D : ℕ) (positive : 0<D)
    (full : ∀v∈S,Nat.card (G.neighborSet v)=D)
    (ends : ∀v∈S,∀w,G.Adj v w → w∈B ∨ w∈A) :
    (D-1)*S.ncard≤(G.induce B).edgeSet.ncard-matchingEdges (G.induce B)+crossCount G S A := by
  classical
  let H := G.induce B
  let T : Set B := {v | v.val∈S}
  let _ := Fintype.ofFinite S
  let _ := Fintype.ofFinite T
  let e := labelImageEquiv B S inc
  have eq (v:S) : Nat.card (H.neighborSet (e v).val)+(G.neighborSet v.val∩A).ncard=D := by
    rw [induced_degree_intersection]
    change (G.neighborSet v.val∩B).ncard+(G.neighborSet v.val∩A).ncard=D
    have sep : Disjoint (G.neighborSet v.val∩B) (G.neighborSet v.val∩A) := dis.mono Set.inter_subset_right Set.inter_subset_right
    have all : (G.neighborSet v.val∩B)∪(G.neighborSet v.val∩A)=G.neighborSet v.val := by
      ext w
      exact ⟨fun h => h.elim And.left And.left,fun h => (ends v.val v.property w h).elim
        (fun wb => Or.inl ⟨h,wb⟩) (fun wa => Or.inr ⟨h,wa⟩)⟩
    rw [←Set.ncard_union_eq sep,all,←Nat.card_coe_set_eq,full v.val v.property]
  have sumD : originalDegreeSum H T=∑v:T,Nat.card (H.neighborSet v.val) := by
    apply Finset.sum_subtype
    intro v;exact Set.Finite.mem_toFinset _
  have counted : (∑v:S,Nat.card (H.neighborSet (e v).val))=originalDegreeSum H T := by
    rw [sumD];exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have total := Finset.sum_congr (s₁:=(Finset.univ : Finset S)) rfl (fun v _ => eq v)
  rw [Finset.sum_add_distrib,counted,←crossCount_eq_neighbor_sum,Finset.sum_const,Finset.card_univ,
    ←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,nsmul_eq_mul] at total
  have small := independent_degree_cost H T (fun {v} hv {w} hw ne edge => ind hv hw (fun h => ne (Subtype.ext h)) edge)
  have card : T.ncard=S.ncard := subset_card_on_surviving_labels B S inc
  rw [card] at small
  have mult : S.ncard*D=(D-1)*S.ncard+S.ncard := by
    calc
      S.ncard*D = ((D-1)+1)*S.ncard := by rw [Nat.sub_add_cancel positive,Nat.mul_comm]
      _ = _ := by rw [Nat.add_mul,one_mul]
  simp only [Nat.cast_id] at total
  rw [mult] at total
  change originalDegreeSum H T≤(G.induce B).edgeSet.ncard-matchingEdges (G.induce B)+S.ncard at small
  omega

#print axioms choose_full_exterior_independent
#print axioms exterior_independent_degree_price
end JSP452Audit.StarHost
