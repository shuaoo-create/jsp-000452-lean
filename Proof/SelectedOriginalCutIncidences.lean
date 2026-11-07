import UnrepresentedEightDegreeTightCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

noncomputable def selectedCutVertexEquiv {X:Type u} (G:SimpleGraph X) (A:Set X)
    (B:Set (G.induce Aᶜ).ConnectedComponent) :
    ((C:↥B) × C.val.supp) ≃ ↥(regionCore G A B) := by
  let f (z:(C:↥B) × C.val.supp) : ↥(regionCore G A B) :=
    ⟨z.2.val.val,⟨z.2.val,rfl,(show (G.induce Aᶜ).connectedComponentMk z.2.val=z.1.val from z.2.property).symm ▸ z.1.property⟩⟩
  apply Equiv.ofBijective f ⟨?_,?_⟩
  · rintro ⟨c,x⟩ ⟨d,y⟩ eq
    have raw : x.val.val=y.val.val := congrArg (fun w:↥(regionCore G A B) => w.val) eq
    have vertex : x.val=y.val := Subtype.ext raw
    have source : (G.induce Aᶜ).connectedComponentMk x.val=c.val := x.property
    have dest : (G.induce Aᶜ).connectedComponentMk y.val=d.val := y.property
    have cd : c=d := Subtype.ext (source.symm.trans ((congrArg _ vertex).trans dest))
    subst d
    exact congrArg (Sigma.mk c) (Subtype.ext vertex)
  · rintro ⟨x,v,rfl,mem⟩
    exact ⟨⟨⟨(G.induce Aᶜ).connectedComponentMk v,mem⟩,⟨v,rfl⟩⟩,rfl⟩

theorem selected_cut_cross_sum {X:Type u} [Finite X] (G:SimpleGraph X) (A:Set X)
    (B:Set (G.induce Aᶜ).ConnectedComponent) [Fintype B] (T:Set X) :
    crossCount G (regionCore G A B) T=∑C:↥B,crossCount G (cutPieceSet G A C.val) T := by
  classical
  let _ := Fintype.ofFinite ↥(regionCore G A B)
  let _ (C:↥B) := Fintype.ofFinite ↥C.val.supp
  let f (v:X) := (G.neighborSet v∩T).ncard
  have single (C:↥B) : crossCount G (cutPieceSet G A C.val) T=∑x:C.val.supp,f x.val.val := by
    let _ := Fintype.ofFinite ↥(cutPieceSet G A C.val)
    rw [crossCount_eq_neighbor_sum]
    exact (Fintype.sum_equiv (cutPieceVertexEquiv G A C.val) (fun x:C.val.supp => f x.val.val)
      (fun y:↥(cutPieceSet G A C.val) => f y.val) (fun _ => rfl)).symm
  simp_rw [single]
  rw [crossCount_eq_neighbor_sum]
  have eq := Fintype.sum_equiv (selectedCutVertexEquiv G A B) (fun x:((C:↥B) × C.val.supp) => f x.2.val.val)
    (fun y:↥(regionCore G A B) => f y.val) (fun _ => rfl)
  rw [Fintype.sum_sigma] at eq
  exact eq.symm

theorem uniform_member_odd_size_boundary {X:Type u} [Finite X] (G:SimpleGraph X)
    (a b:ℕ) (odd:Odd a) (S T:Set X) (C:(G.induce (S∪T)ᶜ).ConnectedComponent)
    (mem:C∈uniformOddPieces G a b S T) :
    Odd (Nat.card C.supp+crossCount G (cutPieceSet G (S∪T) C) T) := by
  classical
  let _ := Fintype.ofFinite X
  let P := uniformCaps G a b
  let C' : P.CoreComponent S T := C
  let _ := Fintype.ofFinite C'.supp
  let _ := Fintype.ofFinite ↥(cutPieceSet G (S∪T) C)
  have f (x:X) : Nat.card {w:G.neighborSet x // w.val∈T}=(G.neighborSet x∩T).ncard := by
    let e : {w:G.neighborSet x // w.val∈T} ≃ ↥(G.neighborSet x∩T) := {
      toFun := fun w => ⟨w.val.val,w.val.property,w.property⟩
      invFun := fun y => ⟨⟨y.val,y.property.1⟩,y.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact Nat.card_congr e
  have same : P.toCoreCount (S:=S) (T:=T) C'=crossCount G (cutPieceSet G (S∪T) C) T := by
    rw [crossCount_eq_neighbor_sum]
    change (∑u:C'.supp,Nat.card {w:G.neighborSet u.val.val // w.val∈T})=_
    simp_rw [f]
    let e : ↥C'.supp ≃ ↥(cutPieceSet G (S∪T) C) := cutPieceVertexEquiv G (S∪T) C
    exact Fintype.sum_equiv e (fun x:C'.supp => (G.neighborSet x.val.val∩T).ncard)
      (fun x:↥(cutPieceSet G (S∪T) C) => (G.neighborSet x.val∩T).ncard) (fun _ => rfl)
  change C'∈P.originalTightOdd S T at mem
  have parity := mem.2
  change Odd ((∑_u:C'.supp,a)+P.toCoreCount (S:=S) (T:=T) C') at parity
  rw [same] at parity
  simp only [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id] at parity
  rw [Nat.odd_iff,Nat.add_mod,Nat.mul_mod,Nat.odd_iff.mp odd,Nat.mul_one,Nat.mod_mod] at parity
  rw [Nat.odd_iff,Nat.add_mod]
  exact parity

#print axioms selectedCutVertexEquiv
#print axioms selected_cut_cross_sum
#print axioms uniform_member_odd_size_boundary
end JSP452Audit.StarHost
