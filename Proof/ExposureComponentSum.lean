import RegionComponentLayerBudget
import MinimumExposure

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

private theorem exposure_matching_comap_closed {X Y : Type*} {G : SimpleGraph X} {J : SimpleGraph Y}
    (e : G ↪g J) {M : J.Subgraph} (hM : M.IsMatching)
    (closed : ∀ x y, J.Adj (e x) y → ∃ z, e z = y) : (M.comap e.toHom).IsMatching := by
  intro x hx
  obtain ⟨y,edge,unique⟩ := hM hx
  obtain ⟨z,rfl⟩ := closed x y (M.adj_sub edge)
  exact ⟨z,⟨e.map_rel_iff.mp (M.adj_sub edge),edge⟩,
    fun w ew => e.injective (unique (e w) ew.2)⟩

private theorem minimumExposure_le_iso {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (f : G ≃g H) (D : ℕ) :
    minimumExposure G D ≤ minimumExposure H D := by
  obtain ⟨M,hm,max,att⟩ := minimumExposure_attained H D
  have hn := exposure_matching_comap_closed f.toEmbedding hm (fun _ y _ => f.surjective y)
  have support : (M.comap f.toHom).verts.ncard=M.verts.ncard :=
    Set.ncard_preimage_of_injective_subset_range f.injective (fun y _ => f.surjective y)
  rw [matching_vertices_eq_twice_edges hn,matching_vertices_eq_twice_edges hm,
    max,← rank_eq_of_graph_iso f] at support
  have maximal : (M.comap f.toHom).edgeSet.ncard=matchingEdges G := by
    change 2*(M.comap f.toHom).edgeSet.ncard=2*matchingEdges G at support
    omega
  have exposed : exposedFull G (M.comap f.toHom) D=f ⁻¹' exposedFull H M D := by
    ext x
    have deg := Nat.card_congr (f.mapNeighborSet x)
    change (f x ∉ M.verts ∧ _=D) ↔ (f x ∉ M.verts ∧ _=D)
    rw [deg]
  have price := minimumExposure_le G D (M.comap f.toHom) hn maximal
  rw [exposed,Set.ncard_preimage_of_injective_subset_range f.injective
    (fun y _ => f.surjective y),att] at price
  exact price

/-- The minimizing parameter is invariant under a genuine graph isomorphism;
the matching being transported remains maximum. -/
theorem minimumExposure_iso {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ≃g H) (D : ℕ) :
    minimumExposure G D = minimumExposure H D :=
  le_antisymm (minimumExposure_le_iso e D) (minimumExposure_le_iso e.symm D)

private theorem degree_sum_left {X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y) (x : X) :
    Nat.card ((G ⊕g H).neighborSet (.inl x))=Nat.card (G.neighborSet x) := by
  rw [Nat.card_coe_set_eq,neighborSet_sum_inl,
    Set.ncard_image_of_injective _ Sum.inl_injective,Nat.card_coe_set_eq]

private theorem degree_sum_right {X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y) (y : Y) :
    Nat.card ((G ⊕g H).neighborSet (.inr y))=Nat.card (H.neighborSet y) := by
  rw [Nat.card_coe_set_eq,neighborSet_sum_inr,
    Set.ncard_image_of_injective _ Sum.inr_injective,Nat.card_coe_set_eq]

/-- Minimum full-degree exposure adds over an actual disjoint graph sum. -/
theorem minimumExposure_sumGraph {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y) (D : ℕ) :
    minimumExposure (G ⊕g H) D = minimumExposure G D+minimumExposure H D := by
  let l : G ↪g G ⊕g H := Embedding.sumInl
  let r : H ↪g G ⊕g H := Embedding.sumInr
  apply le_antisymm
  · obtain ⟨M,hm,maxM,attM⟩ := minimumExposure_attained G D
    obtain ⟨N,hn,maxN,attN⟩ := minimumExposure_attained H D
    let L := M.map l.toHom
    let R := N.map r.toHom
    have apart : Disjoint L.verts R.verts := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨x,_,rfl⟩ ⟨y,_,same⟩
      change (Sum.inr y : X ⊕ Y) = Sum.inl x at same
      contradiction
    have merged := matching_sup_of_disjoint_verts (G ⊕g H)
      (hm.map l.toHom l.injective) (hn.map r.toHom r.injective) apart
    have count : (L ⊔ R).verts.ncard = M.verts.ncard+N.verts.ncard := by
      change (L.verts ∪ R.verts).ncard = _
      rw [Set.ncard_union_eq apart]
      rw [show L.verts=l '' M.verts from rfl,show R.verts=r '' N.verts from rfl,
        Set.ncard_image_of_injective _ l.injective,Set.ncard_image_of_injective _ r.injective]
    rw [matching_vertices_eq_twice_edges merged,matching_vertices_eq_twice_edges hm,
      matching_vertices_eq_twice_edges hn,maxM,maxN] at count
    have maximal : (L ⊔ R).edgeSet.ncard=matchingEdges (G ⊕g H) := by
      rw [matchingEdges_sumGraph]
      dsimp [L,R]
      omega
    have expL : Sum.inl ⁻¹' exposedFull (G ⊕g H) (L ⊔ R) D=exposedFull G M D := by
      ext x
      change (Sum.inl x ∉ (L ⊔ R).verts ∧ Nat.card ((G ⊕g H).neighborSet (.inl x))=D) ↔ _
      rw [degree_sum_left]
      simp [exposedFull,L,R,l,r,eq_comm]
    have expR : Sum.inr ⁻¹' exposedFull (G ⊕g H) (L ⊔ R) D=exposedFull H N D := by
      ext y
      change (Sum.inr y ∉ (L ⊔ R).verts ∧ Nat.card ((G ⊕g H).neighborSet (.inr y))=D) ↔ _
      rw [degree_sum_right]
      simp [exposedFull,L,R,l,r,eq_comm]
    have price : (exposedFull (G ⊕g H) (L ⊔ R) D).ncard=
        (exposedFull G M D).ncard+(exposedFull H N D).ncard := by
      have split := (Nat.card_congr (Equiv.subtypeSum
        (p := fun z => z ∈ exposedFull (G ⊕g H) (L ⊔ R) D))).trans Nat.card_sum
      change _=(Sum.inl ⁻¹' exposedFull _ _ _).ncard+(Sum.inr ⁻¹' exposedFull _ _ _).ncard at split
      rwa [expL,expR] at split
    exact (minimumExposure_le _ D (L ⊔ R) merged maximal).trans_eq
      (price.trans (congrArg₂ (·+·) attM attN))
  · obtain ⟨M,hm,max,att⟩ := minimumExposure_attained (G ⊕g H) D
    have lm := exposure_matching_comap_closed l hm (by
      rintro x (y|y) adj
      · exact ⟨y,rfl⟩
      · exact False.elim (not_adj_sum_inl_inr x y adj))
    have rm := exposure_matching_comap_closed r hm (by
      rintro x (y|y) adj
      · exact False.elim (not_adj_sum_inl_inr y x adj.symm)
      · exact ⟨y,rfl⟩)
    have verts : M.verts.ncard=(M.comap l.toHom).verts.ncard+(M.comap r.toHom).verts.ncard :=
      (Nat.card_congr (Equiv.subtypeSum (p := fun z => z ∈ M.verts))).trans Nat.card_sum
    rw [matching_vertices_eq_twice_edges hm,max,matchingEdges_sumGraph,
      matching_vertices_eq_twice_edges lm,matching_vertices_eq_twice_edges rm] at verts
    have ll := le_matchingEdges lm
    have rl := le_matchingEdges rm
    have lmax : (M.comap l.toHom).edgeSet.ncard=matchingEdges G := by omega
    have rmax : (M.comap r.toHom).edgeSet.ncard=matchingEdges H := by omega
    have expL : Sum.inl ⁻¹' exposedFull (G ⊕g H) M D=exposedFull G (M.comap l.toHom) D := by
      ext x
      change (Sum.inl x ∉ M.verts ∧ Nat.card ((G ⊕g H).neighborSet (.inl x))=D) ↔ _
      rw [degree_sum_left]
      rfl
    have expR : Sum.inr ⁻¹' exposedFull (G ⊕g H) M D=exposedFull H (M.comap r.toHom) D := by
      ext y
      change (Sum.inr y ∉ M.verts ∧ Nat.card ((G ⊕g H).neighborSet (.inr y))=D) ↔ _
      rw [degree_sum_right]
      rfl
    have price : (exposedFull (G ⊕g H) M D).ncard=
        (exposedFull G (M.comap l.toHom) D).ncard+(exposedFull H (M.comap r.toHom) D).ncard := by
      have split := (Nat.card_congr (Equiv.subtypeSum
        (p := fun z => z ∈ exposedFull (G ⊕g H) M D))).trans Nat.card_sum
      change _=(Sum.inl ⁻¹' exposedFull _ _ _).ncard+(Sum.inr ⁻¹' exposedFull _ _ _).ncard at split
      rwa [expL,expR] at split
    exact (Nat.add_le_add (minimumExposure_le G D _ lm lmax)
      (minimumExposure_le H D _ rm rmax)).trans_eq (price.symm.trans att)

/-- A separation of original labels gives an exact exposure decomposition. -/
theorem minimumExposure_split_regions {X : Type*} [Finite X] (G : SimpleGraph X)
    (K P Q : Set X) (D : ℕ) (cover : P∪Q=K) (apart : Disjoint P Q)
    (sep : ∀ x∈P, ∀ y∈Q, ¬G.Adj x y) :
    minimumExposure (G.induce K) D = minimumExposure (G.induce P) D+minimumExposure (G.induce Q) D := by
  rw [← minimumExposure_iso (regionSumIso G K P Q cover apart sep) D,minimumExposure_sumGraph]

/-- The global optimum is exactly the sum of the optima on all actual components.
No connectedness, positive degree, or nonempty-host assumption is required. -/
theorem minimumExposure_component_total {X : Type*} [Finite X] (G : SimpleGraph X)
    [Fintype G.ConnectedComponent] (D : ℕ) :
    minimumExposure G D = ∑ c : G.ConnectedComponent, minimumExposure c.toSimpleGraph D := by
  classical
  let U (T : Finset G.ConnectedComponent) : Set X := {x | G.connectedComponentMk x ∈ T}
  have part (T : Finset G.ConnectedComponent) :
      minimumExposure (G.induce (U T)) D = ∑ c ∈ T, minimumExposure c.toSimpleGraph D := by
    induction T using Finset.induction_on with
    | empty =>
      let H := G.induce (U ∅)
      let _ : IsEmpty ↥(U ∅) := ⟨fun x => Finset.notMem_empty _ x.property⟩
      obtain ⟨M,_,_,att⟩ := minimumExposure_attained H D
      have empty : exposedFull H M D=∅ := Set.eq_empty_of_forall_notMem (fun x => isEmptyElim x)
      rw [empty,Set.ncard_empty] at att
      simpa only [Finset.sum_empty] using att.symm
    | @insert c T fresh ih =>
      have cover : c.supp ∪ U T = U (insert c T) := by ext x; exact Finset.mem_insert.symm
      have apart : Disjoint c.supp (U T) := Set.disjoint_left.mpr fun _ hx ht =>
        fresh ((show G.connectedComponentMk _ = c from hx) ▸ ht)
      have sep : ∀ x∈c.supp, ∀ y∈U T, ¬G.Adj x y := fun _ hx _ hy edge =>
        Set.disjoint_left.mp apart ((c.mem_supp_congr_adj edge).mp hx) hy
      rw [minimumExposure_split_regions G _ _ _ D cover apart sep,ih,Finset.sum_insert fresh]
      rfl
  have result := part Finset.univ
  have all : U Finset.univ=Set.univ := by ext x; simp [U]
  rw [all,minimumExposure_iso (induceUnivIso G) D] at result
  exact result

/-- The same equality on any selected family of residual components, expressed
on the original-label core and the genuine local component graphs. -/
theorem minimumExposure_region_core {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (T : Set (G.induce Sᶜ).ConnectedComponent) [Fintype T] (D : ℕ) :
    minimumExposure (G.induce (regionCore G S T)) D = ∑ c : T, minimumExposure c.val.toSimpleGraph D := by
  classical
  let H := G.induce (regionCore G S T)
  let _ := Fintype.ofFinite H.ConnectedComponent
  calc
    minimumExposure H D = ∑ c : H.ConnectedComponent, minimumExposure c.toSimpleGraph D :=
      minimumExposure_component_total H D
    _ = ∑ c : T, minimumExposure c.val.toSimpleGraph D :=
      Fintype.sum_equiv (coreComponentEquiv G S T) _ _ (fun c => minimumExposure_iso (coreComponentIso G S T c) D)

#print axioms minimumExposure_iso
#print axioms minimumExposure_sumGraph
#print axioms minimumExposure_component_total
#print axioms minimumExposure_region_core
end JSP452Audit.StarHost
