import ExactInternalCapacityForAnySelectedSetWithAtMostOneEdge
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G K h)
def available := W.support\W.innerTips
def liftInside (I:Set W.available) : Set X := Subtype.val '' I
def innerCut (I:Set W.available) := W.innerTips∪W.liftInside I

theorem inner_stage_seed_account (cap:∀v,Nat.card (G.neighborSet v)≤10) (I:Set W.available)
    (stage:CompleteDegreeStage (G.induce W.available) 10 I) :
    W.innerCut I⊆W.support ∧ (W.innerCut I).ncard=W.innerTips.ncard+I.ncard ∧
    (G.induce (W.innerCut I)).edgeSet.ncard=(G.induce W.innerTips).edgeSet.ncard ∧
    rootShortfall G (W.innerCut I) 10=rootShortfall G W.innerTips 10 ∧
    (W.innerCut I).ncard+W.targetPorts≤W.rank ∧
    G.edgeSet.ncard+W.seedLoss=(G.induce (W.innerCut I)ᶜ).edgeSet.ncard+10*(W.innerCut I).ncard := by
  let T := W.innerTips
  let A := W.liftInside I
  let S := W.innerCut I
  have incT : T⊆W.support := fun _ m => m.1
  have incA : A⊆W.available := by rintro _ ⟨v,_,rfl⟩;exact v.property
  have dis : Disjoint T A := Set.disjoint_left.mpr (fun _ t a => (incA a).2 t)
  have sub : S⊆W.support := Set.union_subset incT (incA.trans Set.sdiff_subset)
  have card : A.ncard=I.ncard := Set.ncard_image_of_injective I Subtype.val_injective
  have sum : S.ncard=T.ncard+A.ncard := Set.ncard_union_eq dis
  have all (x) (hx:x∈A) : Nat.card (G.neighborSet x)=10 := by
    obtain ⟨v,hv,rfl⟩ := hx
    exact Nat.le_antisymm (cap _) ((stage.2.1 _ hv).symm.le.trans (induced_neighbor_count_le G W.available v))
  have zero : crossCount G T A=0 := by
    apply crossCount_of_no_edges
    rintro x hx y ⟨v,hv,rfl⟩ e
    exact (all_neighbors_survive_of_induced_full G W.available v 10 (cap _) (stage.2.1 _ hv) x e.symm).2 hx
  have empty : G.induce A=⊥ := by
    ext x y
    obtain ⟨v,hv,e₁⟩ := x.property
    obtain ⟨w,hw,e₂⟩ := y.property
    refine ⟨fun edge => ?_,False.elim⟩
    have meet : (G.induce W.available).Adj v w := by change G.Adj v.val w.val;rw [e₁,e₂];exact edge
    exact stage.1 hv hw meet.ne meet
  have actual := induced_edges_on_disjoint_union G T A dis
  rw [empty,edgeSet_bot,Set.ncard_empty,zero,Nat.add_zero] at actual
  change (G.induce S).edgeSet.ncard=(G.induce T).edgeSet.ncard at actual
  have fees := original_degree_sum_of_disjoint_union G T A dis
  rw [degree_sum_full G A 10 all] at fees
  change originalDegreeSum G S=originalDegreeSum G T+10*A.ncard at fees
  have same : rootShortfall G S 10=rootShortfall G T 10 := by dsimp only [rootShortfall];rw [sum,fees,Nat.mul_add];omega
  have tips := W.tip_count
  have few := W.defect
  have simple := twice_edges_le_simple_order (G.induce T)
  change 2*(G.induce T).edgeSet.ncard≤T.ncard*(T.ncard-1) at simple
  change T.ncard≤W.portCount at tips
  change W.targetDefect+W.portCount≤2 at few
  have one : (G.induce T).edgeSet.ncard≤1 := by
    rcases (show T.ncard=0 ∨ T.ncard=1 ∨ T.ncard=2 by omega) with a|a|a <;> rw [a] at simple <;> omega
  have fit := W.seed_sized_sets_fit_internal_rank cap S sub (actual.trans_le one)
  have price := root_deletion_cost_with_slack G S 10 (fun v _ => cap v)
  change G.edgeSet.ncard+rootShortfall G S 10+(G.induce S).edgeSet.ncard=_ at price
  rw [same,actual] at price
  exact ⟨sub,by change S.ncard=T.ncard+I.ncard;omega,actual,same,fit,by change G.edgeSet.ncard+(rootShortfall G T 10+(G.induce T).edgeSet.ncard)=(G.induce Sᶜ).edgeSet.ncard+10*S.ncard;omega⟩

#print axioms inner_stage_seed_account
end JSP452Audit.StarHost.TenPortSupport
