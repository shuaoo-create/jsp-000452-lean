import OddCapacityCutPieces
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def portlessUniformPieces {X:Type u} [Finite X] (G:SimpleGraph X) (a b:ℕ) (S T:Set X) :
    Set (G.induce (S∪T)ᶜ).ConnectedComponent :=
  {C|C∈uniformOddPieces G a b S T ∧ crossCount G (cutPieceSet G (S∪T) C) (S∪T)=0}

theorem uniform_tight_piece_full {X:Type u} [Finite X] (G:SimpleGraph X) (a b:ℕ)
    (cap:∀v,Nat.card (G.neighborSet v)≤a+b) (S T:Set X)
    (C:(G.induce (S∪T)ᶜ).ConnectedComponent) (mem:C∈uniformOddPieces G a b S T)
    (x:X) (hx:x∈cutPieceSet G (S∪T) C) : Nat.card (G.neighborSet x)=a+b := by
  classical
  let _ := Fintype.ofFinite X
  let P := uniformCaps G a b
  have caps (v:X) : P.G.degree v≤P.A v+P.B v := by change G.degree v≤a+b;simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using cap v
  change C∈P.originalTightOdd S T at mem
  obtain ⟨v,hv,rfl⟩ := hx
  have exact' := (P.coreTight_iff_degree C caps).mp mem.1 ⟨v,hv⟩
  change G.degree v.val=a+b at exact'
  simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using exact'

theorem portless_uniform_properties {X : Type u} [Finite X] (G : SimpleGraph X) (a b : ℕ)
    (bound : ∀x,Nat.card (G.neighborSet x)≤a+b) (S T : Set X)
    (C : (G.induce (S∪T)ᶜ).ConnectedComponent) (hc : C∈portlessUniformPieces G a b S T) :
    let J := originalComponentOfCutPiece G (S∪T) C
    Odd (Nat.card J.supp) ∧ ∀v∈J.supp,Nat.card (G.neighborSet v)=a+b := by
  classical
  let _ := Fintype.ofFinite X
  intro J
  let A := S∪T
  let P := uniformCaps G a b
  obtain ⟨mem,zero⟩ := hc
  change C∈P.originalTightOdd S T at mem
  change crossCount G (cutPieceSet G A C) A=0 at zero
  have caps (z:X) : P.G.degree z≤P.A z+P.B z := by
    change G.degree z≤a+b
    simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using bound z
  have global : J.supp=cutPieceSet G A C := no_port_piece_is_global G A C zero
  have tight := (P.coreTight_iff_degree C caps).1 mem.1
  have full (z:X) (mem:z∈J.supp) : Nat.card (G.neighborSet z)=a+b := by
    rw [global] at mem
    obtain ⟨w,win,rfl⟩ := mem
    have exact' := tight ⟨w,win⟩
    change G.degree w.val=a+b at exact'
    simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using exact'
  refine ⟨?_,full⟩
  let C' : P.CoreComponent S T := C
  let _ : Fintype ↥C'.supp := Fintype.ofFinite C'.supp
  have toward : P.toCoreCount (S:=S) (T:=T) C'=0 := by
    apply Finset.sum_eq_zero
    intro w _
    have empty : IsEmpty {v:P.G.neighborSet w.val.val // v.val∈T} := ⟨fun v =>
      no_edge_when_port_zero G zero (show w.val.val∈cutPieceSet G A C from ⟨w.val,w.property,rfl⟩) (Or.inr v.property) v.val.property⟩
    let _ := empty;simp
  have parity := mem.2
  change Odd ((∑_w:C'.supp,a)+P.toCoreCount (S:=S) (T:=T) C') at parity
  rw [toward,Nat.add_zero] at parity
  simp only [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul] at parity
  have oc : Odd (Nat.card C.supp) := (Nat.odd_mul.mp parity).1
  have sizes := Nat.card_congr (cutPieceVertexEquiv G A C)
  rw [global];exact sizes ▸ oc

theorem portless_uniform_count {X : Type u} [Finite X] (G : SimpleGraph X) (a b : ℕ)
    (cap : ∀x,Nat.card (G.neighborSet x)≤a+b) (S T : Set X) :
    (portlessUniformPieces G a b S T).ncard≤(oddRegularComponents G (a+b)).ncard := by
  classical
  let A := S∪T
  let N := portlessUniformPieces G a b S T
  let Z := oddRegularComponents G (a+b)
  let index (c:↥N) : ↥Z :=
    ⟨originalComponentOfCutPiece G A c.val,portless_uniform_properties G a b cap S T c.val c.property⟩
  have inj : Function.Injective index := by
    intro c e eq
    have same : originalComponentOfCutPiece G A c.val=originalComponentOfCutPiece G A e.val :=
      congrArg (fun z:↥Z => z.val) eq
    have eqc := no_port_piece_is_global G A c.val c.property.2
    have eqe := no_port_piece_is_global G A e.val e.property.2
    have regions : cutPieceSet G A c.val=cutPieceSet G A e.val := eqc.symm.trans ((congrArg ConnectedComponent.supp same).trans eqe)
    let v := c.val.nonempty_supp.choose
    have inc : v∈c.val.supp := c.val.nonempty_supp.choose_spec
    have mem : v.val∈cutPieceSet G A e.val := regions ▸ (show v.val∈cutPieceSet G A c.val from ⟨v,inc,rfl⟩)
    obtain ⟨w,ew,eqw⟩ := mem
    have equal : w=v := Subtype.ext eqw
    rw [equal] at ew
    apply Subtype.ext
    change (G.induce Aᶜ).connectedComponentMk v=c.val at inc
    change (G.induce Aᶜ).connectedComponentMk v=e.val at ew
    exact inc.symm.trans ew
  have size := Nat.card_le_card_of_injective index inj
  simpa only [Nat.card_coe_set_eq] using size

#print axioms uniform_tight_piece_full
#print axioms portless_uniform_properties
#print axioms portless_uniform_count
end JSP452Audit.StarHost
