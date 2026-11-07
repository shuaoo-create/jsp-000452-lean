import ZeroReserveIndependentCuts
import MissedNeighbor

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Original labels of the actual matching partners of I except its exposed
vertex, keeping the condition that the partner survives the cut explicit. -/
def independentMateLabels {X : Type*} (Q : SimpleGraph X) (I : Set X) (v : X)
    (M : Q.Subgraph) : Set X :=
  {w | w∉I ∧ ∃i, i∈I ∧ i≠v ∧ M.Adj i w}

/-- Restrict actual edges to surviving endpoints. A point whose old partner
was removed is not left as an isolated point of the matching support. -/
def restrictedOutsideMatching {X : Type*} (Q : SimpleGraph X) (I : Set X)
    (M : Q.Subgraph) : (Q.induce Iᶜ).Subgraph where
  verts := {x | ∃y : ↥(Iᶜ : Set X), M.Adj x.val y.val}
  Adj x y := M.Adj x.val y.val
  adj_sub := fun edge => M.adj_sub edge
  edge_vert := fun edge => ⟨_,edge⟩
  symm := ⟨fun _ _ edge => edge.symm⟩

@[simp] theorem restrictedOutsideMatching_adj {X : Type*} (Q : SimpleGraph X)
    (I : Set X) (M : Q.Subgraph) (x y : ↥(Iᶜ : Set X)) :
    (restrictedOutsideMatching Q I M).Adj x y ↔ M.Adj x.val y.val := Iff.rfl

theorem restrictedOutsideMatching_isMatching {X : Type*} (Q : SimpleGraph X)
    (I : Set X) (M : Q.Subgraph) (hm : M.IsMatching) :
    (restrictedOutsideMatching Q I M).IsMatching := by
  rintro x ⟨y,edge⟩
  exact ⟨y,edge,fun z other => Subtype.ext (hm.eq_of_adj_left other edge)⟩

theorem restrictedOutsideMatching_uncovered {X : Type*} (Q : SimpleGraph X)
    (I : Set X) (v : X) (vi : v∈I) (M : Q.Subgraph) (hm : M.IsMatching)
    (expose : M.verts={x | x≠v}) (x : ↥(Iᶜ : Set X)) :
    x∉(restrictedOutsideMatching Q I M).verts ↔ x.val∈independentMateLabels Q I v M := by
  constructor
  · intro uncovered
    have old : x.val∈M.verts := by
      rw [expose]
      exact fun eq => x.property (eq.symm ▸ vi)
    obtain ⟨i,edge,_⟩ := hm old
    have inside : i∈I := by
      by_contra outside
      exact uncovered ⟨⟨i,outside⟩,edge⟩
    have ne : i≠v := by
      have used := M.edge_vert edge.symm
      rwa [expose] at used
    exact ⟨x.property,i,inside,ne,edge.symm⟩
  · rintro ⟨_,i,inside,_,edge⟩ ⟨y,xy⟩
    have same : y.val=i := hm.eq_of_adj_left xy edge.symm
    exact y.property (same.symm ▸ inside)

theorem independentMateLabels_card {X : Type*} [Finite X] (Q : SimpleGraph X)
    (I : Set X) (indep : Q.IsIndepSet I) (v : X) (vi : v∈I)
    (M : Q.Subgraph) (hm : M.IsMatching) (expose : M.verts={x | x≠v}) :
    (independentMateLabels Q I v M).ncard+1=I.ncard := by
  classical
  let A := I\{v}
  have partner (i : A) : ∃w, M.Adj i.val w := by
    have active : i.val∈M.verts := by
      rw [expose]
      exact i.property.2
    obtain ⟨w,edge,_⟩ := hm active
    exact ⟨w,edge⟩
  choose mate edge using partner
  have outside (i : A) : mate i∉I := by
    intro inside
    exact indep i.property.1 inside (M.adj_sub (edge i)).ne (M.adj_sub (edge i))
  let code (i : A) : independentMateLabels Q I v M :=
    ⟨mate i,outside i,i.val,i.property.1,i.property.2,edge i⟩
  have inj : Function.Injective code := by
    intro i j same
    have eq : mate i=mate j := congrArg Subtype.val same
    exact Subtype.ext (hm.eq_of_adj_right (edge i) (eq.symm ▸ edge j))
  have onto : Function.Surjective code := by
    rintro ⟨w,_,i,inside,ne,iw⟩
    let a : A := ⟨i,inside,ne⟩
    exact ⟨a,Subtype.ext (hm.eq_of_adj_left (edge a) iw)⟩
  have count : A.ncard=(independentMateLabels Q I v M).ncard :=
    Nat.card_congr (Equiv.ofBijective code ⟨inj,onto⟩)
  rw [← count]
  exact Set.ncard_sdiff_singleton_add_one vi

/-- For every near-perfect original matching exposing a vertex of an
independent set, its genuine restriction is maximum and exposes exactly the
distinct partners of the other cut vertices. Those partner labels are independent. -/
theorem independent_mate_barrier {X : Type*} [Finite X] (Q : SimpleGraph X) (D : ℕ)
    (pos : 0<D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (crit : PerfectAfterEveryDeletion Q) (zero : baseReserve Q D=0)
    (I : Set X) (indep : Q.IsIndepSet I) (v : X) (vi : v∈I)
    (M : Q.Subgraph) (hm : M.IsMatching) (expose : M.verts={x | x≠v}) :
    let N := restrictedOutsideMatching Q I M
    let W := independentMateLabels Q I v M
    N.IsMatching ∧ N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ) ∧
      Subtype.val '' (N.vertsᶜ) = W ∧ W.ncard+1=I.ncard ∧ Q.IsIndepSet W := by
  intro N W
  let _ : Nonempty X := ⟨v⟩
  have matching : N.IsMatching := restrictedOutsideMatching_isMatching Q I M hm
  have missed := restrictedOutsideMatching_uncovered Q I v vi M hm expose
  have image : Subtype.val '' (N.vertsᶜ) = W := by
    ext w
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (missed x).mp hx
    · intro hw
      exact ⟨⟨w,hw.1⟩,(missed ⟨w,hw.1⟩).mpr hw,rfl⟩
  have card : W.ncard+1=I.ncard := independentMateLabels_card Q I indep v vi M hm expose
  have holes : N.vertsᶜ.ncard=W.ncard := by
    rw [← image,Set.ncard_image_of_injective _ Subtype.val_injective]
  have support := Set.ncard_add_ncard_compl N.verts
  rw [matching_vertices_eq_twice_edges matching,holes,Nat.card_coe_set_eq] at support
  have all := Set.ncard_add_ncard_compl I
  have order := factorCritical_order_rank Q crit v
  have ranks := (zero_reserve_independent_cut Q D pos reg crit zero I ⟨v,vi⟩ indep).2.1
  have maximum : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ) := by omega
  refine ⟨matching,maximum,image,card,?_⟩
  intro x hx y hy _ adjacent
  let a : ↥(Iᶜ : Set X) := ⟨x,hx.1⟩
  let b : ↥(Iᶜ : Set X) := ⟨y,hy.1⟩
  have xa : a∉N.verts := (missed a).mpr hx
  have yb : b∉N.verts := (missed b).mpr hy
  exact yb (missed_neighbors_subset (Q.induce Iᶜ) N matching maximum xa adjacent)

#print axioms independentMateLabels_card
#print axioms independent_mate_barrier
end JSP452Audit.StarHost
