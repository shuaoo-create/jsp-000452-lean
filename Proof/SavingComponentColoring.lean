import RegularCenterSaving
import FlexibleComponents
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- A single regular critical component gives a strictly cheaper dominating
set for the nonisolated vertices of the original graph. Each other component
pays at most its true matching rank, including empty-edge components. -/
theorem global_centers_with_saving_component (G : SimpleGraph X) (D : ℕ)
    (c : G.ConnectedComponent) (four : 4≤D)
    (reg : ∀v:c.supp,Nat.card (c.toSimpleGraph.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion c.toSimpleGraph) (evenD : Even D) :
    ∃S : Set X,S.ncard<matchingEdges G ∧
      ∀x,(∃y,G.Adj x y) → x∉S → ∃z∈S,G.Adj x z := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  have pick (b : G.ConnectedComponent) : ∃T : Set b.supp,
      T.ncard≤matchingEdges b.toSimpleGraph ∧ (b=c → T.ncard<matchingEdges b.toSimpleGraph) ∧
      ∀x,(∃y,b.toSimpleGraph.Adj x y) → x∉T → ∃z∈T,b.toSimpleGraph.Adj x z := by
    by_cases eq : b=c
    · subst b
      let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
      obtain ⟨T,lt,dom⟩ := regular_centers_save_one c.toSimpleGraph D four evenD reg crit
      exact ⟨T,lt.le,fun _ => lt,fun x _ hx => dom x hx⟩
    · obtain ⟨T,size,dom⟩ := centers_at_matching_rank b.toSimpleGraph
      exact ⟨T,size,fun h => (eq h).elim,dom⟩
  choose T bound strict covered using pick
  let L (b : G.ConnectedComponent) : Set X := Subtype.val '' T b
  let S := ⋃b,L b
  have apart : Pairwise (Function.onFun Disjoint L) := by
    intro b d ne
    apply Set.disjoint_left.mpr
    rintro x ⟨v,_,rfl⟩ ⟨w,_,eq⟩
    have vb : G.connectedComponentMk v.val=b := v.property
    have wd : G.connectedComponentMk w.val=d := w.property
    exact ne (vb.symm.trans ((congrArg G.connectedComponentMk eq).symm.trans wd))
  have count := Set.ncard_iUnion_of_finite (fun b => Set.toFinite (L b)) apart
  have local_size (b : G.ConnectedComponent) : (L b).ncard=(T b).ncard :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  have saved := Finset.sum_lt_sum (s:=Finset.univ)
    (fun b _ => bound b) ⟨c,Finset.mem_univ _,strict c rfl⟩
  have total := (component_rank_budget_gluing G).1
  refine ⟨S,?_,?_⟩
  · change (⋃ b,L b).ncard < matchingEdges G
    rw [count,finsum_eq_sum_of_fintype,total]
    simpa only [local_size] using saved
  · intro x noniso outside
    let b := G.connectedComponentMk x
    let v : b.supp := ⟨x,rfl⟩
    obtain ⟨y,xy⟩ := noniso
    let u : b.supp := ⟨y,(ConnectedComponent.sound xy.reachable).symm⟩
    have out : v∉T b := fun h => outside (Set.mem_iUnion.mpr ⟨b,⟨v,h,rfl⟩⟩)
    obtain ⟨z,zt,vz⟩ := covered b v ⟨u,xy⟩ out
    exact ⟨z.val,Set.mem_iUnion.mpr ⟨b,⟨z,zt,rfl⟩⟩,vz⟩

theorem saving_component_coloring (G : SimpleGraph X) (D : ℕ)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (c : G.ConnectedComponent) (four : 4≤D)
    (reg : ∀v:c.supp,Nat.card (c.toSimpleGraph.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion c.toSimpleGraph) (evenD : Even D) :
    ∃R : SimpleGraph X,R≤G ∧ (∀x,Nat.card (R.neighborSet x)≤D-1) ∧
      matchingEdges (G \ R)<matchingEdges G := by
  obtain ⟨S,size,dom⟩ := global_centers_with_saving_component G D c four reg crit evenD
  have hits (x : X) (deg : Nat.card (G.neighborSet x)=D) (out : x∉S) : ∃z∈S,G.Adj x z := by
    rw [Nat.card_coe_set_eq] at deg
    have noniso := (Set.ncard_pos (Set.toFinite (G.neighborSet x))).mp (by omega)
    exact dom x noniso out
  obtain ⟨R,sub,capR,blue⟩ := coloring_from_centers G D (by omega) cap S hits
  exact ⟨R,sub,capR,blue.trans_lt size⟩

#print axioms global_centers_with_saving_component
#print axioms saving_component_coloring
end JSP452Audit.StarHost
