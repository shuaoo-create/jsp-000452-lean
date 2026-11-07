import NineVertexNonneighborTriples
namespace JSP452Audit.StarHost
open SimpleGraph

def threeByThreeHost : SimpleGraph (Fin 3×Fin 3) where
  Adj x y := x.1≠y.1
  symm := ⟨fun _ _ e => e.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

theorem physical_nine_vertex_iso {X:Type*} [Finite X] (Q:SimpleGraph X) (order:Nat.card X=9)
    (reg:∀v,Nat.card (Q.neighborSet v)=6) (stages:∀A:Set X,CompleteDegreeStage Q 6 A → 3≤A.ncard) :
    Nonempty (Q ≃g threeByThreeHost) := by
  classical
  have agree := nonneighbor_sets_agree_at_nine Q order reg stages
  let s : Setoid X := {
    r := fun x y => ¬Q.Adj x y
    iseqv := ⟨fun x => Q.loopless.irrefl x,fun h e => h e.symm,by
      intro x y z noXY noYZ
      have yz : z∈(Q.neighborSet y)ᶜ := noYZ
      rw [←agree x y noXY] at yz
      exact yz⟩ }
  let f := Quotient.mk s
  let K := Quotient s
  let _ := Fintype.ofFinite X
  let _ := Fintype.ofFinite K
  have fiber (k:K) : Nat.card {v:X // f v=k}=3 := by
    obtain ⟨v,rfl⟩ := Quotient.exists_rep k
    let A := (Q.neighborSet v)ᶜ
    have eq (w:X) : f w=f v ↔ w∈A := by
      exact ⟨fun h e => (show ¬Q.Adj w v from Quotient.exact h) e.symm,
        fun no => Quotient.sound (show ¬Q.Adj w v from fun e => no e.symm)⟩
    have equiv := Equiv.subtypeEquivRight eq
    have total := Set.ncard_add_ncard_compl (Q.neighborSet v)
    have deg : (Q.neighborSet v).ncard=6 := reg v
    have card : A.ncard=3 := by dsimp [A];omega
    exact (Nat.card_congr equiv).trans card
  let table (k:K) : {v:X // f v=k} ≃ Fin 3 := Fintype.equivFinOfCardEq
    (Nat.card_eq_fintype_card.symm.trans (fiber k))
  have sum := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Nat.card_sigma] at sum
  change (∑k:K,Nat.card {v:X // f v=k})=Nat.card X at sum
  simp only [fiber,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,order] at sum
  have three : Fintype.card K=3 := by omega
  let label : K ≃ Fin 3 := Fintype.equivFinOfCardEq three
  let chart : X ≃ (Fin 3×Fin 3) :=
    ((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight table)).trans
      ((Equiv.sigmaEquivProd K (Fin 3)).trans (Equiv.prodCongr label (Equiv.refl _)))
  have group (x:X) : (chart x).1=label (f x) := rfl
  refine ⟨{toEquiv := chart,map_rel_iff' := ?_}⟩
  intro x y
  change (chart x).1≠(chart y).1 ↔ Q.Adj x y
  rw [group,group,label.injective.ne_iff]
  exact ⟨fun ne => Classical.byContradiction (fun h => ne (Quotient.sound (show s.r x y from h))),
    fun edge eq => (show ¬Q.Adj x y from Quotient.exact eq) edge⟩

#print axioms physical_nine_vertex_iso
end JSP452Audit.StarHost
