import TypedColumnInventoryOnEveryActualCutOfThePayableExterior
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] (G:SimpleGraph X)

structure PeakRemoval (U:Set X) where
  removed : Set X
  fee : ℕ
  extendsCut : U⊆removed
  size : removed.ncard=min (U.ncard+1) (Nat.card X)
  edgeCount : (G.induce Uᶜ).edgeSet.ncard=(G.induce removedᶜ).edgeSet.ncard+fee
  cap : ∀v:↥(Uᶜ:Set X),Nat.card ((G.induce Uᶜ).neighborSet v)≤fee
  attained : fee=0 ∨ ∃v:↥(Uᶜ:Set X),Nat.card ((G.induce Uᶜ).neighborSet v)=fee
  vertex : U≠Set.univ → ∃v:↥(Uᶜ:Set X),removed=outerCut U {v} ∧ Nat.card ((G.induce Uᶜ).neighborSet v)=fee

theorem peak_removal_exists (U:Set X) : Nonempty (PeakRemoval G U) := by
  classical
  by_cases full:U=Set.univ
  · subst U
    refine ⟨⟨Set.univ,0,fun _ h => h,by simp,by simp,?_,Or.inl rfl,fun bad => (bad rfl).elim⟩⟩
    intro v;exact (v.property (Set.mem_univ _)).elim
  have living : (Uᶜ:Set X).Nonempty := by
    by_contra! none
    exact full (by simpa using congrArg (fun W:Set X => Wᶜ) none)
  obtain ⟨x,hx⟩ := living
  let H := G.induce Uᶜ
  let _ := Fintype.ofFinite ↥(Uᶜ:Set X)
  obtain ⟨v,_,high⟩ := Finset.exists_max_image Finset.univ (fun z => Nat.card (H.neighborSet z))
    (show (Finset.univ:Finset ↥(Uᶜ:Set X)).Nonempty from ⟨⟨x,hx⟩,Finset.mem_univ _⟩)
  let d := Nat.card (H.neighborSet v)
  let V := outerCut U {v}
  have count : V.ncard=U.ncard+1 := by rw [outerCut_ncard,Set.ncard_singleton]
  have limit : V.ncard≤Nat.card X := Set.ncard_le_card _
  have distinct : H.IsIndepSet ({v}:Set ↥(Uᶜ:Set X)) := by
    intro a ha b hb ne
    exact (ne ((Set.mem_singleton_iff.mp ha).trans (Set.mem_singleton_iff.mp hb).symm)).elim
  have loss := JSP452Audit.StarHost.degree_on_independent_full_set H {v} d (by intro w hw;rw [Set.mem_singleton_iff.mp hw]) distinct
  have e := nestedCutIso G U ({v}:Set ↥(Uᶜ:Set X))
  have edge : (H.induce ({v}ᶜ:Set ↥(Uᶜ:Set X))).edgeSet.ncard=(G.induce Vᶜ).edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  refine ⟨⟨V,d,Set.subset_union_left,by omega,?_,fun w => high w (Finset.mem_univ w),
      Or.inr ⟨v,rfl⟩,fun _ => ⟨v,rfl,rfl⟩⟩⟩
  simpa only [edge,Set.ncard_singleton,Nat.mul_one] using loss

theorem nested_original_degree (S T:Set X) (sub:S⊆T) (v:↥(Tᶜ:Set X)) :
    let old : ↥(Sᶜ:Set X) := ⟨v.val,fun hs => v.property (sub hs)⟩
    Nat.card ((G.induce Tᶜ).neighborSet v)≤Nat.card ((G.induce Sᶜ).neighborSet old) := by
  intro old
  let f (w:(G.induce Tᶜ).neighborSet v) : (G.induce Sᶜ).neighborSet old :=
    ⟨⟨w.val.val,fun hs => w.val.property (sub hs)⟩,w.property⟩
  exact Nat.card_le_card_of_injective f (fun _ _ eq =>
    Subtype.ext (Subtype.ext (congrArg (fun w:(G.induce Sᶜ).neighborSet old => w.val.val) eq)))

#print axioms peak_removal_exists
#print axioms nested_original_degree
end JSP452Audit.StarHost
