import CrossMateBlocks
import ActualBlockSmall
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- In any collection C of pointed blocks, independent labels number at
most |C|+1. Add all exposed vertices outside C before using the global cap. -/
theorem many_blocks_independent_bound (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges H)
    (limit : ∀A : Set X,H.IsIndepSet A → A.ncard≤N.vertsᶜ.ncard+1)
    (C : Set X) (holes : C⊆N.vertsᶜ) (S : Set X) (ind : H.IsIndepSet S)
    (inside : ∀x∈S,∃w∈C,x∈mateBlock H N w) : S.ncard≤C.ncard+1 := by
  let V := N.vertsᶜ \ C
  have outside (u : X) (hu : u∈V) (w : X) (hw : w∈C) : u∈N.vertsᶜ \ {w} :=
    ⟨hu.1,fun eq => hu.2 ((Set.mem_singleton_iff.mp eq).symm ▸ hw)⟩
  have apart : Disjoint S V := by
    apply Set.disjoint_left.mpr
    intro x hx other
    obtain ⟨w,hw,col⟩ := inside x hx
    exact Set.disjoint_left.mp (mateBlock_disjoint_other_holes H N w) col (outside x other w hw)
  have forbid (x : X) (hx : x∈S) (u : X) (hu : u∈V) : ¬H.Adj x u := by
    obtain ⟨w,hw,col⟩ := inside x hx
    exact mateBlock_separated H N hm max (holes hw) x col u (outside u hu w hw)
  have united : H.IsIndepSet (S∪V) := by
    rintro a (sa|ua) b (sb|ub) ne edge
    · exact ind sa sb ne edge
    · exact forbid a sa b ub edge
    · exact forbid b sb a ua edge.symm
    · exact ub.1 (missed_neighbors_subset H N hm max ua.1 edge)
  have cost := limit _ united
  have sub := Set.ncard_le_ncard holes
  rw [Set.ncard_union_eq apart] at cost
  dsimp [V] at cost
  rw [Set.ncard_sdiff holes] at cost
  omega

/-- The bound on the same original maximum-independent-set decomposition,
including every selected subfamily of actual residual holes. -/
theorem actual_many_blocks_independent_bound (Q : SimpleGraph X) (D : ℕ) (pos : 0<D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (zero : baseReserve Q D=0) (I : Set X) (indI : Q.IsIndepSet I)
    (maxI : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (v : X) (vi : v∈I) (M : Q.Subgraph) (hm : M.IsMatching) (expose : M.verts={x|x≠v}) :
    let H := Q.induce Iᶜ
    let N := restrictedOutsideMatching Q I M
    ∀C : Set ↥(Iᶜ : Set X),C⊆N.vertsᶜ → ∀S : Set ↥(Iᶜ : Set X),H.IsIndepSet S →
      (∀x∈S,∃w∈C,x∈mateBlock H N w) → S.ncard≤C.ncard+1 := by
  intro H N
  obtain ⟨matchN,rank,labels,gap,_⟩ := independent_mate_barrier Q D pos reg crit zero I indI v vi M hm expose
  rw [←labels,Set.ncard_image_of_injective _ Subtype.val_injective] at gap
  apply many_blocks_independent_bound H N matchN rank
  intro A hA
  have imageInd : Q.IsIndepSet (Subtype.val '' A) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ne adj
    exact hA ha hb (fun eq => ne (congrArg Subtype.val eq)) adj
  have cap := maxI _ imageInd
  rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←gap] at cap

omit [Finite X] in
private theorem nonclique_independent_pair (H : SimpleGraph X) (A : Set X) (bad : ¬H.IsClique A) :
    ∃S : Set X,S⊆A ∧ S.ncard=2 ∧ H.IsIndepSet S := by
  classical
  have pair : ∃x∈A,∃y∈A,x≠y ∧ ¬H.Adj x y := by
    by_contra! all
    exact bad (fun {x} hx {y} hy ne => all x hx y hy ne)
  obtain ⟨x,hx,y,hy,ne,away⟩ := pair
  refine ⟨{x,y},?_,Set.ncard_pair ne,?_⟩
  · rintro z (rfl|eq)
    · exact hx
    · exact (Set.mem_singleton_iff.mp eq).symm ▸ hy
  · intro a ha b hb dif adj
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;>
      first | exact dif rfl | exact away adj | exact away adj.symm

/-- Two distinct nonclique blocks must have a cross edge. Otherwise the
two independent pairs extend the other holes beyond the allowed cap. -/
theorem two_nonclique_blocks_touch (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges H)
    (limit : ∀A : Set X,H.IsIndepSet A → A.ncard≤N.vertsᶜ.ncard+1)
    (w u : X) (hw : w∉N.verts) (hu : u∉N.verts) (ne : w≠u)
    (bw : ¬H.IsClique (mateBlock H N w)) (bu : ¬H.IsClique (mateBlock H N u)) :
    ∃x∈mateBlock H N w,∃y∈mateBlock H N u,H.Adj x y := by
  classical
  by_contra! away
  obtain ⟨A,Ain,twoA,indA⟩ := nonclique_independent_pair H _ bw
  obtain ⟨B,Bin,twoB,indB⟩ := nonclique_independent_pair H _ bu
  have dis := (different_mate_blocks_disjoint H N hm max w u hw hu ne).mono Ain Bin
  have independent : H.IsIndepSet (A∪B) := by
    rintro x (xa|xb) y (ya|yb) dif adj
    · exact indA xa ya dif adj
    · exact away x (Ain xa) y (Bin yb) adj
    · exact away y (Ain ya) x (Bin xb) adj.symm
    · exact indB xb yb dif adj
  have inHoles : ({w,u} : Set X)⊆N.vertsᶜ := by
    rintro z (rfl|eq)
    · exact hw
    · exact (Set.mem_singleton_iff.mp eq).symm ▸ hu
  have bound := many_blocks_independent_bound H N hm max limit {w,u} inHoles (A∪B) independent
    (by rintro x (ha|hb)
        · exact ⟨w,Or.inl rfl,Ain ha⟩
        · exact ⟨u,Or.inr rfl,Bin hb⟩)
  rw [Set.ncard_union_eq dis,twoA,twoB,Set.ncard_pair ne] at bound
  omega

theorem critical_nonclique_block_unique (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges H)
    (limit : ∀A : Set X,H.IsIndepSet A → A.ncard≤N.vertsᶜ.ncard+1)
    (w u : X) (hw : w∉N.verts) (hu : u∉N.verts)
    (bw : ¬H.IsClique (mateBlock H N w)) (bu : ¬H.IsClique (mateBlock H N u))
    (cw : PerfectAfterEveryDeletion (H.induce (mateBlock H N w)))
    (cu : PerfectAfterEveryDeletion (H.induce (mateBlock H N u))) : w=u := by
  by_contra ne
  obtain ⟨x,hx,y,hy,adj⟩ := two_nonclique_blocks_touch H N hm max limit w u hw hu ne bw bu
  exact critical_mate_blocks_separated H N hm max w u hw hu ne cw cu x hx y hy adj

#print axioms two_nonclique_blocks_touch
#print axioms critical_nonclique_block_unique

#print axioms many_blocks_independent_bound
#print axioms actual_many_blocks_independent_bound
end JSP452Audit.StarHost
