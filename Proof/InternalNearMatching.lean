import FactorCriticalPeak

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Combine actual near-perfect internal matchings, omitting precisely the selected
original label in each component and all vertices of the cut S. -/
theorem internal_matching_away_from_picks (G : SimpleGraph X) (S : Set X)
    (crit : ∀ c : (G.induce Sᶜ).ConnectedComponent,
      PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp))
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, ↥c.supp) :
    ∃ P : G.Subgraph, P.IsMatching ∧ ∀ v : X, v ∈ P.verts ↔
      ∃ (c : (G.induce Sᶜ).ConnectedComponent) (x : ↥c.supp), x.val.val = v ∧ x ≠ pick c := by
  classical
  let Y := G.induce Sᶜ
  have localMatch (c : Y.ConnectedComponent) :
      ∃ P : (Y.induce c.supp).Subgraph, P.IsMatching ∧ P.verts = {x | x ≠ pick c} := by
    obtain ⟨M,perf⟩ := crit c (pick c)
    obtain ⟨P,hm,hv,_⟩ := lift_perfect_off_vertex_maximum (Y.induce c.supp) (pick c) M perf
    exact ⟨P,hm,hv⟩
  choose P hP verts using localMatch
  let e (c : Y.ConnectedComponent) : Y.induce c.supp ↪g G := {
    toFun := fun x => x.val.val
    inj' := fun _ _ h => Subtype.ext (Subtype.ext h)
    map_rel_iff' := Iff.rfl }
  let N (c : Y.ConnectedComponent) := (P c).map (e c).toHom
  have matchN (c : Y.ConnectedComponent) : (N c).IsMatching := (hP c).map (e c).toHom (e c).injective
  have mem (c : Y.ConnectedComponent) (v : X) :
      v ∈ (N c).verts ↔ ∃ x : c.supp, x.val.val = v ∧ x ≠ pick c := by
    change (∃ x ∈ (P c).verts, (e c) x = v) ↔ _
    rw [verts]
    exact ⟨fun ⟨x,ne,h⟩ => ⟨x,h,ne⟩,fun ⟨x,h,ne⟩ => ⟨x,ne,h⟩⟩
  have dis : Pairwise fun c d => Disjoint (N c).support (N d).support := by
    intro c d neq
    apply Set.disjoint_left.mpr
    intro v hc hd
    obtain ⟨x,hx,_⟩ := (mem c v).mp ((N c).support_subset_verts hc)
    obtain ⟨y,hy,_⟩ := (mem d v).mp ((N d).support_subset_verts hd)
    have eq : x.val = y.val := Subtype.ext (hx.trans hy.symm)
    exact neq (ConnectedComponent.eq_of_common_vertex x.property (eq ▸ y.property))
  refine ⟨⨆ c, N c,Subgraph.IsMatching.iSup matchN dis,?_⟩
  intro v
  rw [Subgraph.verts_iSup,Set.mem_iUnion]
  exact exists_congr (fun c => mem c v)

#print axioms internal_matching_away_from_picks
end JSP452Audit.StarHost
