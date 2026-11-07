import FullForestEndpointGuards
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- All roots of the selected region belong to its original tight
barrier. Thus the strong endpoint retains their full cardinality. -/
theorem original_root_endpoint_guards (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let a := K.roots.ncard
    let d := F.rank-matchingEdges F.G
    a+F.r+2*(d+∑i,(F.n i-1)/2)≤F.t ∧ a+F.r+2*(d+∑j,(F.m j-1)/2)≤F.s := by
  intro a d
  have small := (minimal_rank_exact_source F paid).2.2.1
  have pos : 0<d := by dsimp [d];omega
  have balance : matchingEdges F.G+d=rowCount F.s F.t F.r := by change _=F.rank;dsimp [d];omega
  have pack := full_row_endpoint_guards F.G F.hs F.ht F.n F.m F.pn F.pm F.row K.barrier K.tight
    (fun c => (K.critical c).2) d pos balance
  have sub : K.roots⊆K.barrier := by rintro _ ⟨u,_,rfl⟩;exact u.property
  have bound : a≤K.barrier.ncard := Set.ncard_le_ncard sub
  exact ⟨by omega,by omega⟩

/-- Apply the same theorem to the larger fixed exterior residual.
The additional rank delta survives twice inside the endpoint price. -/
theorem escaping_exterior_endpoint {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d : ℕ)
    (ht : 0<t) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (pos : 0<d)
    (esc : matchingEdges (G.induce K.core)<s) (data : CompleteExteriorData G K n m r N d) :
    let μ := matchingEdges (G.induce K.core)
    let W := componentBudget (G.induce K.core) n
    let δ := μ-W.loss
    let a := K.roots.ncard
    a+r+2*(d+∑j,(m j-1)/2)+δ≤s-μ ∧
      a+r+2*(d+δ+∑i,(W.entries n i-1)/2)≤t := by
  intro μ W δ a
  obtain ⟨_,fit,row,rank,_,_⟩ := data
  change W.loss≤μ at fit
  have live : 0<W.len := by dsimp [RemovalBudget.len];change μ<s at esc;omega
  let B := G.induce K.rest
  obtain ⟨S,tight,crit⟩ := exists_critical_barrier B
  have cost := full_row_endpoint_guards B live ht (W.entries n) m (W.entries_positive n pn) pm row
    S tight (fun c => (crit c).2) (d+δ) (by omega)
    (by change rowCount W.len t (r+a)=matchingEdges B+d+δ at rank;change matchingEdges B+(d+δ)=rowCount W.len t (r+a);omega)
  change S.ncard+(r+a)+2*(d+δ+∑i,(W.entries n i-1)/2)≤t ∧
    S.ncard+(r+a)+2*(d+δ+∑j,(m j-1)/2)≤W.len at cost
  have len : W.len=s-W.loss := rfl
  change μ<s at esc
  dsimp only [δ] at cost ⊢
  exact ⟨by omega,by omega⟩

theorem strict_exterior_endpoint_guards (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let H := F.G.induce K.core
    let μ := matchingEdges H
    let a := K.roots.ncard
    let d := F.rank-matchingEdges F.G
    (μ<F.s → a+F.r+2*(d+∑j,(F.m j-1)/2)+(μ-(componentBudget H F.n).loss)≤F.s-μ) ∧
    (μ<F.t → a+F.r+2*(d+∑i,(F.n i-1)/2)+(μ-(componentBudget H F.m).loss)≤F.t-μ) := by
  intro H μ a d
  have pos : 2≤d := (minimal_strict_source_deficit F paid).2.2
  obtain ⟨red,blue⟩ := strict_both_complete_exteriors F paid K
  exact ⟨fun esc => (escaping_exterior_endpoint _ _ _ _ _ _ d F.ht F.pn F.pm (by omega) esc (red esc)).1,
    fun esc => (escaping_exterior_endpoint _ _ _ _ _ _ d F.hs F.pm F.pn (by omega) esc (blue esc)).1⟩

#print axioms original_root_endpoint_guards
#print axioms escaping_exterior_endpoint
#print axioms strict_exterior_endpoint_guards
end JSP452Audit.StarHost
