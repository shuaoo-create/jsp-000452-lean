import OptimalMatchingEndpointCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def uniformCaps {X:Type u} (G:SimpleGraph X) (a b:ℕ) : JSP452Audit.Padded.Spec X := ⟨G,fun _ => a,fun _ => b,false⟩

noncomputable def uniformOddPieces {X:Type u} [Finite X] (G:SimpleGraph X) (a b:ℕ) (S T:Set X) :
    Set (G.induce (S∪T)ᶜ).ConnectedComponent := by
  classical
  let _ := Fintype.ofFinite X
  exact (uniformCaps G a b).originalTightOdd S T

theorem uniform_factor_cut_on_original {X:Type u} [Finite X] (G:SimpleGraph X) (a b:ℕ) (S T:Set X) :
    originalFactorCut G a b S T=((uniformOddPieces G a b S T).ncard:ℤ)+(crossCount G T S:ℤ)-
      (a:ℤ)*(S.ncard:ℤ)-(b:ℤ)*(T.ncard:ℤ) := by
  classical
  let _ := Fintype.ofFinite X
  let _ := Fintype.ofFinite S
  let _ := Fintype.ofFinite T
  let P := uniformCaps G a b
  change P.cutDeficit S T=_
  unfold JSP452Audit.Padded.Spec.cutDeficit
  rw [actual_factor_cross_edges]
  change ((uniformOddPieces G a b S T).ncard:ℤ)+(crossCount G T S:ℤ)-(∑_x:↥S,a:ℕ)-(∑_y:↥T,b:ℕ)=_
  simp only [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,nsmul_eq_mul,Nat.cast_mul]
  push_cast
  ring

theorem same_odd_capacity_piece_family {X:Type u} [Finite X] (G:SimpleGraph X) (a b c d:ℕ)
    (sum:a+b=c+d) (oa:Odd a) (oc:Odd c) (S T:Set X) :
    uniformOddPieces G a b S T=uniformOddPieces G c d S T := by
  classical
  let _ := Fintype.ofFinite X
  let P := uniformCaps G a b
  let Q := uniformCaps G c d
  ext C
  let _ := Fintype.ofFinite ↥C.supp
  have tight : P.coreTight (S:=S) (T:=T) C ↔ Q.coreTight (S:=S) (T:=T) C := by
    change (∀v, v∈C.supp → a+b-G.degree v.val=0) ↔ (∀v,v∈C.supp → c+d-G.degree v.val=0)
    rw [sum]
  have transfer {m n u:ℕ} (h:Odd m) (h':Odd n) (j:ℕ) : Odd (u*m+j) ↔ Odd (u*n+j) := by
    simp only [Nat.odd_iff];rw [Nat.add_mod,Nat.add_mod (u*n),Nat.mul_mod,Nat.mul_mod u n,Nat.odd_iff.mp h,Nat.odd_iff.mp h']
  have parity (t:ℕ) : Odd (Nat.card C.supp*a+t) ↔ Odd (Nat.card C.supp*c+t) := transfer oa oc t
  constructor
  · intro mem
    refine ⟨tight.mp mem.1,?_⟩
    have h := mem.2
    dsimp only [uniformCaps,P,Q] at h ⊢
    simp only [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id] at h ⊢
    exact (parity _).mp h
  · intro mem
    refine ⟨tight.mpr mem.1,?_⟩
    have h := mem.2
    dsimp only [uniformCaps,P,Q] at h ⊢
    simp only [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id] at h ⊢
    exact (parity _).mpr h

#print axioms uniform_factor_cut_on_original
#print axioms same_odd_capacity_piece_family
end JSP452Audit.StarHost
