import QuinticRemainingHeadRange
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Even when membership of a feasible removal is justified by a vertex
assignment alone, two half-slots cannot be charged to different odd
components for one star. -/
theorem feasible_half_order_budget {s : ℕ} {X : Type*} [Finite X] (H : SimpleGraph X) (n : Fin s→ℕ)
    (crit : ∀c:H.ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph)
    (T : ↥(componentBudget H n).choices) :
    (∑i:↥T.val,(n i.val+1)/2)≤matchingEdges H := by
  classical
  let _ := Fintype.ofFinite H.ConnectedComponent
  obtain ⟨_,pack⟩ := (mem_component_budget H n T.val).mp T.property
  obtain ⟨f,assign⟩ := pack
  let m (z:↥T.val) := n z.val
  let owner (z:↥T.val) := H.connectedComponentMk (f (center m z))
  let A (c:H.ConnectedComponent) := {z:↥T.val | owner z=c}
  have per (c:H.ConnectedComponent) : (∑z:↥(A c),(m z.val+1)/2)≤matchingEdges c.toSimpleGraph := by
    let send (x:Σz:↥(A c),Fin (m z.val+1)) : c.supp :=
      ⟨f ⟨x.1.val,x.2⟩,(assign _ _).symm.trans x.1.property⟩
    have inj : Function.Injective send := by
      rintro ⟨z,i⟩ ⟨w,j⟩ h
      have same := f.injective (congrArg (fun v:c.supp => v.val) h)
      have zw : z=w := Subtype.ext (congrArg (fun v:Vertices m => v.1) same)
      subst w
      have ij : i=j := Fin.ext (congrArg (fun v:Vertices m => v.2.val) same)
      subst j;rfl
    have size := Nat.card_le_card_of_injective send inj
    rw [Nat.card_sigma] at size
    simp only [Nat.card_fin] at size
    have pairs := Finset.sum_le_sum (s:=Finset.univ) (fun (i:↥(A c)) _ =>
      show 2*((m i.val+1)/2)≤m i.val+1 by omega)
    rw [←Finset.mul_sum] at pairs
    have exactOrder := factorCritical_order_rank c.toSimpleGraph (crit c) c.nonempty_supp.to_subtype.some
    change Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 at exactOrder
    omega
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => per c)
  rw [←(component_rank_budget_gluing H).1] at total
  let e := Equiv.sigmaFiberEquiv owner
  have eq := Fintype.sum_equiv e (fun x => (m x.2.val+1)/2) (fun z => (m z+1)/2) (fun _ => rfl)
  rw [Fintype.sum_sigma] at eq
  exact eq ▸ total

theorem unit_residual_full_half_budget {s D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (hn : Antitone n) (esc : matchingEdges (G.induce K.core)<s)
    (unit : originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2=0) :
    originalThresholdCount n 2+(∑i,(n i-1)/2)≤matchingEdges (G.induce K.core) := by
  classical
  let H := G.induce K.core
  let W := componentBudget H n
  have fit : W.loss≤matchingEdges H := component_budget_loss_le _ _
  have live : 0<W.len := by change 0<s-W.loss;change matchingEdges H<s at esc;omega
  obtain ⟨T,all⟩ := one_pattern_removes_all_nonunits n hn W live unit
  have price := feasible_half_order_budget H n (ordinary_core_components_critical G K) T
  let charge (i:Fin s) := (if 2≤n i then 1 else 0)+(n i-1)/2
  have total : (∑i,charge i)=originalThresholdCount n 2+∑i,(n i-1)/2 := by
    simp [charge,Finset.sum_add_distrib,Finset.sum_boole,originalThresholdCount]
  have trunc : (∑i,charge i)=∑i∈T.val,charge i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ outside
    have small : n i<2 := by by_contra! hi;exact outside (all i hi)
    simp [charge,show ¬2≤n i by omega,show (n i-1)/2=0 by omega]
  have bound := Finset.sum_le_sum (s:=T.val) (fun i _ => show charge i≤(n i+1)/2 by dsimp [charge];split <;> omega)
  rw [Finset.sum_subtype T.val (fun _ => Iff.rfl) (fun i:Fin s => (n i+1)/2)] at bound
  exact total ▸ trunc ▸ bound.trans price

#print axioms feasible_half_order_budget
#print axioms unit_residual_full_half_budget
end JSP452Audit.StarHost