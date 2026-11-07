import RobustHalfOrderGap
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type*} [Finite X]

noncomputable def nontrivialCoreCount (H : SimpleGraph X) : ℕ :=
  ({c : H.ConnectedComponent | 0<matchingEdges c.toSimpleGraph} : Set H.ConnectedComponent).ncard

theorem critical_core_active_labels (H : SimpleGraph X)
    (crit : ∀c:H.ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph) :
    ∃V:Set X,V.ncard=2*matchingEdges H+nontrivialCoreCount H ∧
      ∀v w,H.Adj v w → v∈V := by
  classical
  let _ := Fintype.ofFinite H.ConnectedComponent
  let L (c:H.ConnectedComponent) : Set X := if 0<matchingEdges c.toSimpleGraph then c.supp else ∅
  have sub (c:H.ConnectedComponent) : L c⊆c.supp := by
    dsimp [L];split <;> simp
  have apart : Pairwise (Function.onFun Disjoint L) := by
    intro c b ne;apply Set.disjoint_left.mpr
    intro v hv hw
    exact ne ((show H.connectedComponentMk v=c from sub c hv).symm.trans (sub b hw))
  have order (c:H.ConnectedComponent) : c.supp.ncard=2*matchingEdges c.toSimpleGraph+1 :=
    (Nat.card_coe_set_eq _).symm.trans (factorCritical_order_rank c.toSimpleGraph (crit c) c.nonempty_supp.to_subtype.some)
  have sizes (c:H.ConnectedComponent) : (L c).ncard=2*matchingEdges c.toSimpleGraph+(if 0<matchingEdges c.toSimpleGraph then 1 else 0) := by
    by_cases pos : 0<matchingEdges c.toSimpleGraph
    · simp [L,pos,order]
    · simp [L,show matchingEdges c.toSimpleGraph=0 by omega]
  have num : (∑c:H.ConnectedComponent,if 0<matchingEdges c.toSimpleGraph then 1 else 0)=nontrivialCoreCount H := by
    rw [Finset.sum_boole]
    let F := Finset.univ.filter (fun c:H.ConnectedComponent => 0<matchingEdges c.toSimpleGraph)
    have same : (F : Set H.ConnectedComponent)={c | 0<matchingEdges c.toSimpleGraph} := by ext c;simp [F]
    change F.card=_
    rw [←Set.ncard_coe_finset,same];rfl
  refine ⟨⋃c,L c,?_,?_⟩
  · rw [Set.ncard_iUnion_of_finite (fun c => Set.toFinite (L c)) apart,finsum_eq_sum_of_fintype]
    simp_rw [sizes]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←(component_rank_budget_gluing H).1,num]
  · intro v w edge
    let c := H.connectedComponentMk v
    have inside : v∈c.supp := rfl
    have both : w∈c.supp := (c.mem_supp_congr_adj edge).mp inside
    have pos : 0<matchingEdges c.toSimpleGraph := by
      by_contra! none
      have small : c.supp.ncard≤1 := by rw [order];omega
      exact edge.ne ((Set.ncard_le_one (Set.toFinite _)).mp small v inside w both)
    exact Set.mem_iUnion.mpr ⟨c,by simpa [L,pos] using inside⟩

theorem robust_whole_mass {s : ℕ} (H : SimpleGraph X) (n : Fin s→ℕ) (pn : ∀i,1≤n i)
    (crit : ∀c:H.ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph)
    (d : ℕ) (smallD : d≤s) (trigger : s≤matchingEdges H+d)
    (robust : ∀U:Set X,U.ncard≤matchingEdges H+d-s → (forest n).IsContained (H.induce Uᶜ)) :
    (∑i,n i)+d≤matchingEdges H+nontrivialCoreCount H := by
  classical
  let b := matchingEdges H+d-s
  have bsize : b+s=matchingEdges H+d := by dsimp [b];omega
  obtain ⟨V,size,incident⟩ := critical_core_active_labels H crit
  obtain ⟨U,sub,card⟩ := Set.exists_subset_card_eq (s:=V) (show b≤V.ncard by omega)
  obtain ⟨f⟩ := robust U (show U.ncard≤b from card.le)
  let send (z:Vertices n) : ↥(V\U) := ⟨(f z).val,by
    obtain ⟨w,edge⟩ := forest_has_neighbor n pn z
    exact ⟨incident _ _ (f.toHom.map_adj edge), (f z).property⟩⟩
  have bound := Nat.card_le_card_of_injective send (fun a b eq => f.injective (Subtype.ext
    (congrArg (fun y : ↥(V\U) => y.val) eq)))
  change Nat.card (Σi:Fin s,Fin (n i+1))≤Nat.card ↥(V\U) at bound
  rw [Nat.card_sigma,Nat.card_coe_set_eq] at bound
  simp only [Nat.card_fin,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at bound
  have vertices : (∑i,n i)+s≤(V\U).ncard := by simpa using bound
  have rm := Set.ncard_sdiff_add_ncard_of_subset sub
  omega

#print axioms critical_core_active_labels
#print axioms robust_whole_mass
end JSP452Audit.StarHost
