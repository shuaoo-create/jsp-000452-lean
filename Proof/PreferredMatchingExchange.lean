import UniqueOddRegionExit
import EquimatchableReserve
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Retain the old matching away from the preferred part and its unique matched
root. Internally change the exposed point to any vertex exposable in that part. -/
theorem exchange_preferred_exposure (Q : SimpleGraph X) (M : Q.Subgraph) (hm : M.IsMatching)
    (i u : X) (ui : u≠i) (P : Set X) (iOut : i∉P) (uOut : u∉P)
    (supp : M.verts={v | v≠i}) (p : X) (hp : p∈P) (up : M.Adj u p)
    (only : ∀a∈P,∀b,M.Adj a b → b∉P → b=u)
    (z : P) (ex : ExposablePoint (Q.induce P) z) :
    ∃J : Q.Subgraph,J.IsMatching ∧ J.vertsᶜ={i,u,z.val} := by
  classical
  let T := M.verts \ (P∪{u})
  have outer : (M.induce T).IsMatching := by
    intro v hv
    obtain ⟨w,edge,uniq⟩ := hm hv.1
    have outside : w∉P := by
      intro h
      have same := only w h v edge.symm (fun h => hv.2 (Or.inl h))
      exact hv.2 (Or.inr (Set.mem_singleton_iff.mpr same))
    have wu : w≠u := by
      intro eq
      have vw : M.Adj u v := eq ▸ edge.symm
      have same := hm.eq_of_adj_left vw up
      exact hv.2 (Or.inl (same.symm ▸ hp))
    have wt : w∈T := ⟨M.edge_vert edge.symm,fun h => h.elim outside (fun he => wu (Set.mem_singleton_iff.mp he))⟩
    exact ⟨w,⟨hv,wt,edge⟩,fun a h => uniq a h.2.2⟩
  obtain ⟨V,hV⟩ := ex
  obtain ⟨U,um,su,_⟩ := lift_perfect_off_vertex_maximum (Q.induce P) z V hV
  let emb := SimpleGraph.Embedding.induce (G:=Q) P
  let L := U.map emb.toHom
  have lm : L.IsMatching := um.map emb.toHom emb.injective
  have lVerts : L.verts=P\{z.val} := by
    change Subtype.val '' U.verts=P\{z.val}
    rw [su]
    ext v
    constructor
    · rintro ⟨v,h,rfl⟩;exact ⟨v.property,fun eq => h (Subtype.ext (Set.mem_singleton_iff.mp eq))⟩
    · rintro ⟨h,ne⟩
      exact ⟨⟨v,h⟩,fun eq => ne (Set.mem_singleton_iff.mpr (congrArg Subtype.val eq)),rfl⟩
  have dis : Disjoint (M.induce T).verts L.verts := by
    rw [lVerts]
    exact Set.disjoint_left.mpr (fun _ h hp => h.2 (Or.inl hp.1))
  let J := M.induce T ⊔ L
  have jm := JSP452Audit.Padded.matching_sup_of_disjoint_verts Q outer lm dis
  refine ⟨J,jm,?_⟩
  change ((M.induce T).verts∪L.verts)ᶜ={i,u,z.val}
  rw [lVerts]
  change (((M.verts\(P∪{u}))∪(P\{z.val})))ᶜ={i,u,z.val}
  rw [supp]
  ext v
  simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_sdiff,Set.mem_singleton_iff,
    Set.mem_insert_iff,Set.mem_setOf_eq]
  by_cases ei : v=i
  · subst v;simp [iOut]
  by_cases eu : v=u
  · subst v;simp [uOut]
  by_cases ez : v=z.val
  · subst v;simp [z.property]
  by_cases vp : v∈P <;> simp [ei,eu,ez,vp]

/-- A near-perfect matching with an interchangeable preferred endpoint forces
the exposed root and the exit root together to cover all exposable points. -/
theorem roots_cover_exposable_points [Nonempty X] (Q : SimpleGraph X) (D : ℕ) (pos : 1≤D)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (crit : PerfectAfterEveryDeletion Q)
    (zero : baseReserve Q D=0) (M : Q.Subgraph) (hm : M.IsMatching)
    (i u : X) (ui : u≠i) (nonadj : ¬Q.Adj i u) (P : Set X) (iOut : i∉P) (uOut : u∉P)
    (supp : M.verts={v | v≠i}) (p : X) (hp : p∈P) (up : M.Adj u p)
    (only : ∀a∈P,∀b,M.Adj a b → b∉P → b=u)
    (z : P) (ex : ExposablePoint (Q.induce P) z) : Q.Adj i z.val ∨ Q.Adj u z.val := by
  classical
  by_contra! no
  obtain ⟨J,jm,holes⟩ := exchange_preferred_exposure Q M hm i u ui P iOut uOut supp p hp up only z ex
  have ind : Q.IsIndepSet J.vertsᶜ := by
    rw [holes]
    intro a ha b hb diff ab
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
      first | exact diff rfl | exact nonadj ab | exact nonadj ab.symm | exact no.1 ab |
              exact no.1 ab.symm | exact no.2 ab | exact no.2 ab.symm
  have dj : D-1+1=D := by omega
  have biggest := zero_reserve_all_maximal_maximum Q (D-1) (fun v => dj.symm ▸ reg v)
    crit (dj.symm ▸ zero) J jm ((maximal_matching_iff_uncovered_independent Q J jm).mpr ind)
  have count := matching_vertices_eq_twice_edges jm
  have card := Set.ncard_add_ncard_compl J.verts
  have xz : i≠z.val := fun h => iOut (h.symm ▸ z.property)
  have uz : u≠z.val := fun h => uOut (h.symm ▸ z.property)
  rw [holes,Set.ncard_insert_of_notMem (by simp [Ne.symm ui,xz]),Set.ncard_pair uz] at card
  have order := factorCritical_order_rank Q crit i
  omega

#print axioms exchange_preferred_exposure
#print axioms roots_cover_exposable_points
end JSP452Audit.StarHost
