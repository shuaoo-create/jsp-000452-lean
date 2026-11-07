import NoThreeAugment
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} {Q : SimpleGraph X}

/-- Every actual near-perfect matching exposing a vertex other than y
pairs y with a neighbor of the exposed vertex. -/
def GoodPort (Q : SimpleGraph X) (y : X) : Prop :=
  ∀ v, v ≠ y → ∀ M : Q.Subgraph, M.IsMatching → M.verts = {x | x ≠ v} →
    ∀ z, M.Adj y z → Q.Adj v z

/-- Move the unique exposed vertex from v to s by replacing t--s with t--v.
All edges disjoint from the removed pair remain in the new matching. -/
theorem exchange_single_exposure (Q : SimpleGraph X) (M : Q.Subgraph) (hm : M.IsMatching)
    {v t s : X} (verts : M.verts = {x | x ≠ v}) (ts : M.Adj t s) (tv : Q.Adj t v) :
    ∃ N : Q.Subgraph, N.IsMatching ∧ N.verts = {x | x ≠ s} ∧ N.Adj t v ∧
      ∀ {a b : X}, a ≠ t → a ≠ s → b ≠ t → b ≠ s → M.Adj a b → N.Adj a b := by
  classical
  let rest := M.deleteVerts {t,s}
  let one := Q.subgraphOfAdj tv
  have tsNe : t ≠ s := (M.adj_sub ts).ne
  have sv : s ≠ v := by have h := M.edge_vert ts.symm; rwa [verts] at h
  have dis : Disjoint rest.verts one.verts := by
    apply Set.disjoint_left.mpr
    intro a h ha
    change a ∈ M.verts \ ({t,s} : Set X) at h
    change a ∈ ({t,v} : Set X) at ha
    simp only [verts,Set.mem_ofPred_eq,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff] at h ha
    tauto
  have matching := Padded.matching_sup_of_disjoint_verts Q
    (matching_delete_pair Q M hm ts) (Subgraph.IsMatching.subgraphOfAdj tv) dis
  refine ⟨rest ⊔ one,matching,?_,Or.inr (Q.subgraphOfAdj_adj_self tv),?_⟩
  · ext a
    change ((a ∈ M.verts ∧ a ∉ ({t,s} : Set X)) ∨ a ∈ ({t,v} : Set X)) ↔ a ≠ s
    simp only [verts,Set.mem_ofPred_eq,Set.mem_insert_iff,Set.mem_singleton_iff]
    grind
  · intro a b at' as' bt bs edge
    apply Or.inl
    exact Subgraph.deleteVerts_adj.mpr ⟨M.edge_vert edge,by simp [at',as'],
      M.edge_vert edge.symm,by simp [bt,bs],edge⟩

/-- Exterior neighbors of the exposed vertex have distinct matched partners.
The port edge survives each switch used to prove the partner is adjacent to z. -/
theorem good_port_partner_injection (Q : SimpleGraph X) {y v z : X} (good : GoodPort Q y)
    (M : Q.Subgraph) (hm : M.IsMatching) (verts : M.verts = {x | x ≠ v}) (yz : M.Adj y z) :
    Nonempty (↥(Q.neighborSet v \ {y}) ↪ ↥(Q.neighborSet z \ {v})) := by
  classical
  let L := Q.neighborSet v \ {y}
  let R := Q.neighborSet z \ {v}
  have mate (t : L) : ∃ s : X, M.Adj t.val s := by
    have inM : t.val ∈ M.verts := by
      rw [verts]
      exact (show Q.Adj v t.val from t.property.1).ne.symm
    obtain ⟨s,edge,_⟩ := hm inM
    exact ⟨s,edge⟩
  let partner (t : L) := (mate t).choose
  have paired (t : L) : M.Adj t.val (partner t) := (mate t).choose_spec
  have right (t : L) : partner t ∈ R := by
    have edge := paired t
    have sv : partner t ≠ v := by have used := M.edge_vert edge.symm; rwa [verts] at used
    refine ⟨?_,fun h => sv (Set.mem_singleton_iff.mp h)⟩
    by_cases tz : t.val = z
    · have zy : M.Adj t.val y := tz.symm ▸ yz.symm
      have eq := hm.eq_of_adj_left edge zy
      exact eq.symm ▸ (M.adj_sub yz).symm
    have ty : t.val ≠ y := fun h => t.property.2 (Set.mem_singleton_iff.mpr h)
    have sy : partner t ≠ y := by
      intro h
      exact tz (hm.eq_of_adj_right (show M.Adj t.val y from h ▸ edge) yz.symm)
    have sz : partner t ≠ z := by
      intro h
      exact ty (hm.eq_of_adj_right (show M.Adj t.val z from h ▸ edge) yz)
    obtain ⟨N,hN,newVerts,_,kept⟩ := exchange_single_exposure Q M hm verts edge
      (show Q.Adj t.val v from (show Q.Adj v t.val from t.property.1).symm)
    exact (good (partner t) sy N hN newVerts z (kept ty.symm sy.symm (Ne.symm tz) sz.symm yz)).symm
  let f (t : L) : R := ⟨partner t,right t⟩
  have inj : Function.Injective f := by
    intro t u eq
    have same : partner t = partner u := congrArg (fun a : R => a.val) eq
    exact Subtype.ext (hm.eq_of_adj_right (paired t) (same.symm ▸ paired u))
  exact ⟨⟨f,inj⟩⟩

theorem good_port_degree_bound [Finite X] (Q : SimpleGraph X) [DecidableRel Q.Adj]
    {v y z : X} (good : GoodPort Q y) (M : Q.Subgraph) (hm : M.IsMatching)
    (verts : M.verts = {x | x ≠ v}) (yz : M.Adj y z) :
    Nat.card (Q.neighborSet v) + 1 ≤ Nat.card (Q.neighborSet z) + (if Q.Adj v y then 1 else 0) := by
  obtain ⟨f⟩ := good_port_partner_injection Q good M hm verts yz
  have le := Nat.card_le_card_of_injective f f.injective
  change (Q.neighborSet v \ {y}).ncard ≤ (Q.neighborSet z \ {v}).ncard at le
  have yv : y ≠ v := by have h := M.edge_vert yz; rwa [verts] at h
  have vz : v ∈ Q.neighborSet z := (good v yv.symm M hm verts z yz).symm
  have right := Set.ncard_sdiff_add_ncard_of_subset (Set.singleton_subset_iff.mpr vz)
  rw [Set.ncard_singleton] at right
  change (Q.neighborSet v).ncard + 1 ≤ (Q.neighborSet z).ncard + _
  split_ifs with vy
  · have left := Set.ncard_sdiff_add_ncard_of_subset
      (Set.singleton_subset_iff.mpr (show y ∈ Q.neighborSet v from vy))
    rw [Set.ncard_singleton] at left
    omega
  · have dis : Disjoint (Q.neighborSet v) ({y} : Set X) := by
      apply Set.disjoint_left.mpr
      intro w edge hy
      exact vy ((Set.mem_singleton_iff.mp hy) ▸ edge)
    rw [dis.sdiff_eq_left] at le
    omega

#print axioms exchange_single_exposure
#print axioms good_port_partner_injection
#print axioms good_port_degree_bound
end JSP452Audit.StarHost
