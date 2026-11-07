import TheRemainingThirdGapIsLowOrHasExactlyOneOriginalOddRegularComponent
namespace JSP452Audit.StarHost.ScaledPortPlan
open SimpleGraph
universe u
variable {A:Type u} [Finite A] {G:SimpleGraph A} {D k c:ℕ} {K:DegreeRegion G D} (P:ScaledPortPlan K k c)
def portFree : Set ↥P.positives := {Q | crossCount G (cutPieceSet G K.barrier Q.val) K.barrier=0}

theorem genuine_regular_injection :
    (P.portFree).ncard≤(oddRegularComponents G D).ncard := by
  classical
  let f (Q:↥P.portFree) := originalComponentOfCutPiece G K.barrier Q.val.val
  have support (Q:↥P.portFree) : (f Q).supp=cutPieceSet G K.barrier Q.val.val :=
    no_port_piece_is_global G K.barrier Q.val.val Q.property
  have regular (Q:↥P.portFree) : f Q∈oddRegularComponents G D := by
    obtain ⟨z,_,eq⟩ := Q.val.property.1
    have member : Q.val.val∈K.pieces := eq ▸ z.property
    have order : Nat.card (f Q).supp=Nat.card Q.val.val.supp := by
      change (f Q).supp.ncard=_
      rw [support Q];exact (Nat.card_congr (cutPieceVertexEquiv G K.barrier Q.val.val)).symm
    refine ⟨order.symm ▸ (K.critical Q.val.val).1,?_⟩
    intro x hx;rw [support Q] at hx
    obtain ⟨v,hv,rfl⟩ := hx
    exact K.full member ⟨v,hv⟩
  let g (Q:↥P.portFree) : ↥(oddRegularComponents G D) := ⟨f Q,regular Q⟩
  have inj : Function.Injective g := by
    intro Q V common
    have eq : f Q=f V := congrArg Subtype.val common
    have same : cutPieceSet G K.barrier Q.val.val=cutPieceSet G K.barrier V.val.val := (support Q).symm.trans ((congrArg ConnectedComponent.supp eq).trans (support V))
    obtain ⟨x,inside⟩ := Q.val.val.nonempty_supp
    have mem : x.val∈cutPieceSet G K.barrier V.val.val := same.le (by exact ⟨x,inside,rfl⟩)
    obtain ⟨y,hy,matchX⟩ := mem
    have sameX : y=x := Subtype.ext matchX
    exact Subtype.ext (Subtype.ext (ConnectedComponent.eq_of_common_vertex inside (sameX ▸ hy)))
  exact Nat.card_le_card_of_injective g inj

theorem true_internal_hole_budget (cap:∀v,Nat.card (G.neighborSet v)≤D) :
    minimumExposure (G.induce P.paidCore) D≤P.portFree.ncard := by
  classical
  let _ := Fintype.ofFinite ↥P.positives
  have per (Q:↥P.positives) : minimumExposure Q.val.toSimpleGraph D ≤ if Q∈P.portFree then 1 else 0 := by
    by_cases no:Q∈P.portFree
    · rw [if_pos no]
      obtain ⟨v,mem⟩ := Q.val.nonempty_supp
      let x : Q.val.supp := ⟨v,mem⟩
      obtain ⟨M,perfect⟩ := (K.critical Q.val).2 x
      obtain ⟨T,hm,verts,rank⟩ := lift_perfect_off_vertex_maximum Q.val.toSimpleGraph x M perfect
      have cover : exposedFull Q.val.toSimpleGraph T D⊆{x} := by
        intro y miss
        have absent := miss.1
        rw [verts] at absent
        exact Classical.not_not.mp absent
      have bound := Set.ncard_le_ncard cover
      rw [Set.ncard_singleton] at bound
      exact (minimumExposure_le _ D T hm rank).trans bound
    · rw [if_neg no]
      let U := cutPieceSet G K.barrier Q.val
      have live : 0<crossCount G U K.barrier := Nat.pos_of_ne_zero no
      have seen : Nonempty {p:↥U × ↥K.barrier // G.Adj p.1.val p.2.val} := (Nat.card_pos_iff.mp live).1
      obtain ⟨⟨⟨z,a⟩,edge⟩⟩ := seen
      obtain ⟨x,hx,same⟩ := z.property
      have e : G.Adj a.val x.val := same.symm ▸ edge.symm
      have small := root_adjacent_port_low G K.barrier D Q.val ⟨x,hx⟩ a e (cap x.val)
      exact (factorCritical_peak_exposure_zero _ D (K.critical Q.val).2 ⟨x,hx⟩ small).le
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun Q _ => per Q)
  have pay := minimumExposure_region_core G K.barrier P.positives D
  rw [←pay] at sum
  rw [Finset.sum_boole] at sum
  let S := Finset.univ.filter (fun Q:↥P.positives => Q∈P.portFree)
  have eq : (S:Set ↥P.positives)=P.portFree := by ext x;simp [S]
  have card : S.card=P.portFree.ncard := by rw [←eq,Set.ncard_coe_finset]
  exact sum.trans (by change (S.card:ℕ)≤_;exact card.le)

#print axioms genuine_regular_injection
#print axioms true_internal_hole_budget
end JSP452Audit.StarHost.ScaledPortPlan
