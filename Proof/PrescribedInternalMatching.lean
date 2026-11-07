import RealizeRootPlan

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- Lift the supplied internal edges using the original vertex labels, then form
the disjoint union of these component matchings. -/
theorem join_prescribed_internal_matchings (G : SimpleGraph X) (S : Set X)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp)
    (P : ∀ c : (G.induce Sᶜ).ConnectedComponent, ((G.induce Sᶜ).induce c.supp).Subgraph)
    (hP : ∀ c, (P c).IsMatching) (verts : ∀ c, (P c).verts = {x | x ≠ pick c}) :
    ∃ J : G.Subgraph, J.IsMatching ∧
      (∀ v : X, v ∈ J.verts ↔
        ∃ (c : (G.induce Sᶜ).ConnectedComponent) (x : c.supp), x.val.val = v ∧ x ≠ pick c) ∧
      ∀ c (x y : c.supp), (P c).Adj x y → J.Adj x.val.val y.val.val := by
  classical
  let Y := G.induce Sᶜ
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
  refine ⟨⨆ c, N c, Subgraph.IsMatching.iSup matchN dis, ?_, ?_⟩
  · intro v
    rw [Subgraph.verts_iSup, Set.mem_iUnion]
    exact exists_congr (fun c => mem c v)
  · intro c x y edge
    exact Subgraph.iSup_adj.mpr ⟨c, x, y, edge, rfl, rfl⟩

variable [Finite X]

/-- The maximum matching contains every supplied internal edge and every
designated root edge at the same time, with exactly the prescribed holes. -/
theorem realize_prescribed_internal_matching (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (odd : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp))
    (place : ↥S ↪ (G.induce Sᶜ).ConnectedComponent)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp)
    (link : ∀ a : S, G.Adj a.val (pick (place a)).val.val)
    (P : ∀ c : (G.induce Sᶜ).ConnectedComponent, ((G.induce Sᶜ).induce c.supp).Subgraph)
    (matching : ∀ c, (P c).IsMatching) (supports : ∀ c, (P c).verts = {x | x ≠ pick c}) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧
      M.vertsᶜ = freeHoleLabels G S place pick ∧
      (∀ c (x y : c.supp), (P c).Adj x y → M.Adj x.val.val y.val.val) ∧
      (∀ a : S, M.Adj a.val (pick (place a)).val.val) := by
  classical
  let Y := G.induce Sᶜ
  let label (c : Y.ConnectedComponent) := (pick c).val.val
  have labelInj : Function.Injective label := pick_label_injective G S pick
  obtain ⟨J,hP,internals,preserved⟩ := join_prescribed_internal_matchings G S pick P matching supports
  let K := rootEdgeMatching G S place pick link
  have hK := rootEdgeMatching_isMatching G S place pick link
  have roots := rootEdgeMatching_verts G S place pick link
  have internal (v : X) : v ∈ J.verts ↔ v ∉ S ∧ v ∉ Set.range label := by
    constructor
    · intro hv
      obtain ⟨c,x,rfl,diff⟩ := (internals v).mp hv
      refine ⟨x.val.property,?_⟩
      rintro ⟨d,eq⟩
      have same : (pick d).val = x.val := Subtype.ext eq
      have cd : d = c := ConnectedComponent.eq_of_common_vertex (pick d).property (same ▸ x.property)
      subst d
      exact diff (Subtype.ext same.symm)
    · rintro ⟨outside,notPick⟩
      let w : ↥(Sᶜ : Set X) := ⟨v,outside⟩
      let c := Y.connectedComponentMk w
      let x : c.supp := ⟨w,rfl⟩
      refine (internals v).mpr ⟨c,x,rfl,?_⟩
      intro hit
      exact notPick ⟨c,congrArg (fun t : c.supp => t.val.val) hit.symm⟩
  have dis : Disjoint J.verts K.verts := by
    apply Set.disjoint_left.mpr
    intro v p k
    obtain ⟨out,np⟩ := (internal v).mp p
    rcases (roots v).mp k with h | ⟨a,eq⟩
    · exact out h
    · exact np ⟨place a,eq⟩
  have matching := Padded.matching_sup_of_disjoint_verts G hP hK dis
  have holes : (J ⊔ K).vertsᶜ = freeHoleLabels G S place pick := by
    ext v
    constructor
    · intro miss
      change v ∉ J.verts ∪ K.verts at miss
      have outside : v ∉ S := fun h => miss (Or.inr ((roots v).mpr (Or.inl h)))
      have chosen : v ∈ Set.range label := by
        by_contra no
        exact miss (Or.inl ((internal v).mpr ⟨outside,no⟩))
      obtain ⟨c,eq⟩ := chosen
      refine ⟨c,?_,eq⟩
      rintro ⟨a,rfl⟩
      exact miss (Or.inr ((roots v).mpr (Or.inr ⟨a,eq⟩)))
    · rintro ⟨c,free,rfl⟩ used
      rcases used with p | k
      · exact ((internal _).mp p).2 ⟨c,rfl⟩
      · rcases (roots _).mp k with hs | ⟨a,eq⟩
        · exact (pick c).val.property hs
        · exact free ⟨a,labelInj eq⟩
  refine ⟨_, matching, maximum_of_freeHoleLabels G S place pick tight odd _ matching holes,
    holes, ?_, ?_⟩
  · exact fun c x y edge => Or.inl (preserved c x y edge)
  · exact fun a => Or.inr (rootEdgeMatching_edge G S place pick link a)

/-- Prescriptions on an arbitrary set of components suffice. Use the provided
factor-criticality to fill the other components without affecting those edges. -/
theorem realize_partial_internal_matching (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (odd : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp))
    (crit : ∀ c : (G.induce Sᶜ).ConnectedComponent,
      PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp))
    (place : ↥S ↪ (G.induce Sᶜ).ConnectedComponent)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp)
    (link : ∀ a : S, G.Adj a.val (pick (place a)).val.val)
    (chosen : Set (G.induce Sᶜ).ConnectedComponent)
    (P : ∀ c : ↥chosen, ((G.induce Sᶜ).induce c.val.supp).Subgraph)
    (matching : ∀ c, (P c).IsMatching) (supports : ∀ c, (P c).verts = {x | x ≠ pick c.val}) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧
      M.vertsᶜ = freeHoleLabels G S place pick ∧
      (∀ c : ↥chosen, ∀ x y : c.val.supp, (P c).Adj x y → M.Adj x.val.val y.val.val) ∧
      (∀ a : S, M.Adj a.val (pick (place a)).val.val) := by
  classical
  have fill (c : (G.induce Sᶜ).ConnectedComponent) :
      ∃ J : ((G.induce Sᶜ).induce c.supp).Subgraph, J.IsMatching ∧
        J.verts = {x | x ≠ pick c} ∧ ∀ hc : c ∈ chosen, J = P ⟨c, hc⟩ := by
    by_cases hc : c ∈ chosen
    · exact ⟨P ⟨c, hc⟩, matching _, supports _, fun _ => rfl⟩
    · obtain ⟨N, perf⟩ := crit c (pick c)
      obtain ⟨J, hm, hv, _⟩ := lift_perfect_off_vertex_maximum _ (pick c) N perf
      exact ⟨J, hm, hv, fun yes => (hc yes).elim⟩
  choose J hm hv hchosen using fill
  obtain ⟨M, hM, max, holes, keep, roots⟩ :=
    realize_prescribed_internal_matching G S tight odd place pick link J hm hv
  refine ⟨M, hM, max, holes, ?_, roots⟩
  intro c x y edge
  apply keep c.val x y
  rwa [hchosen c.val c.property]

#print axioms realize_partial_internal_matching
#print axioms join_prescribed_internal_matchings
#print axioms realize_prescribed_internal_matching
end JSP452Audit.StarHost
