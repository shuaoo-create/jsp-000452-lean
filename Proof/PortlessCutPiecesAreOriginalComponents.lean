import BalancedDeficiencyNeedsPortlessPieces
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem no_edge_when_port_zero {X : Type u} [Finite X] (G : SimpleGraph X) {A U:Set X}
    (zero : crossCount G U A=0) {x y:X} (inside:x∈U) (cut:y∈A) : ¬G.Adj x y := by
  intro edge
  let L := {p:↥U × ↥A // G.Adj p.1.val p.2.val}
  let _ : Nonempty L := ⟨⟨(⟨x,inside⟩,⟨y,cut⟩),edge⟩⟩
  have yes : 0<Nat.card L := Nat.card_pos
  change Nat.card L=0 at zero;omega

noncomputable def originalComponentOfCutPiece {X : Type u} (G : SimpleGraph X) (A : Set X)
    (C : (G.induce Aᶜ).ConnectedComponent) : G.ConnectedComponent :=
  G.connectedComponentMk C.nonempty_supp.choose.val

theorem no_port_piece_is_global {X : Type u} [Finite X] (G : SimpleGraph X) (A : Set X)
    (C : (G.induce Aᶜ).ConnectedComponent) (zero : crossCount G (cutPieceSet G A C) A=0) :
    (originalComponentOfCutPiece G A C).supp=cutPieceSet G A C := by
  let z := C.nonempty_supp.choose
  have member : z∈C.supp := C.nonempty_supp.choose_spec
  have included : z.val∈cutPieceSet G A C := ⟨z,member,rfl⟩
  have closed (x:X) (mem:x∈cutPieceSet G A C) (y:X) (adj:G.Adj x y) : y∈cutPieceSet G A C :=
    cut_piece_neighbor G A C mem adj (fun hit => no_edge_when_port_zero G zero mem hit adj)
  apply Set.Subset.antisymm (cubic_closed_component G _ z.val included closed)
  rintro x ⟨w,hw,rfl⟩
  have reach := C.reachable_of_mem_supp member hw
  have eq := ConnectedComponent.sound (reach.map (Embedding.induce (G:=G) Aᶜ).toHom)
  exact eq.symm

theorem no_port_piece_properties {X : Type u} [Finite X] (G : SimpleGraph X) (p : ℕ)
    (bound : ∀x,Nat.card (G.neighborSet x)≤2*p) (S T : Set X)
    (C : (G.induce (S∪T)ᶜ).ConnectedComponent) (hc : C∈noPortOddPieces G p S T) :
    let J := originalComponentOfCutPiece G (S∪T) C
    Odd (Nat.card J.supp) ∧ ∀v∈J.supp,Nat.card (G.neighborSet v)=2*p := by
  classical
  let _ := Fintype.ofFinite X
  intro J
  let A := S∪T
  let P := equalFactorCaps G p
  obtain ⟨mem,zero⟩ := hc
  change C∈P.originalTightOdd S T at mem
  change crossCount G (cutPieceSet G A C) A=0 at zero
  have caps (z:X) : P.G.degree z≤P.A z+P.B z := by
    change G.degree z≤p+p
    simpa only [Nat.two_mul,Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using bound z
  have global : J.supp=cutPieceSet G A C := no_port_piece_is_global G A C zero
  have tight := (P.coreTight_iff_degree C caps).1 mem.1
  have full (z:X) (mem:z∈J.supp) : Nat.card (G.neighborSet z)=2*p := by
    rw [global] at mem
    obtain ⟨w,win,rfl⟩ := mem
    have exact' := tight ⟨w,win⟩
    change G.degree w.val=p+p at exact'
    simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree,Nat.two_mul] using exact'
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
  change Odd ((∑_w:C'.supp,p)+P.toCoreCount (S:=S) (T:=T) C') at parity
  rw [toward,Nat.add_zero] at parity
  simp only [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul] at parity
  have oc : Odd (Nat.card C.supp) := (Nat.odd_mul.mp parity).1
  have sizes := Nat.card_congr (cutPieceVertexEquiv G A C)
  rw [global];exact sizes ▸ oc

#print axioms no_edge_when_port_zero
#print axioms no_port_piece_is_global
#print axioms no_port_piece_properties
end JSP452Audit.StarHost