import BalancedCutBoundaryParity
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def equalFactorCaps {X : Type u} (G : SimpleGraph X) (p : ℕ) : JSP452Audit.Padded.Spec X :=
  ⟨G,fun _ => p,fun _ => p,false⟩

theorem actual_factor_cross_edges {X : Type u} [Fintype X] (P : JSP452Audit.Padded.Spec X) [DecidableRel P.G.Adj]
    (S T : Set X) : P.cutCrossTS S T=crossCount P.G T S := by
  let e : ((v:T) × {w:P.G.neighborSet v.val // w.val∈S}) ≃ {z:↥T × ↥S // P.G.Adj z.1.val z.2.val} := {
    toFun := fun v => ⟨⟨v.1,⟨v.2.val.val,v.2.property⟩⟩,v.2.val.property⟩
    invFun := fun z => ⟨z.val.1,⟨⟨z.val.2.val,z.property⟩,z.val.2.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact Nat.card_congr e

noncomputable def noPortOddPieces {X : Type u} [Finite X] (G : SimpleGraph X) (p : ℕ) (S T : Set X) :
    Set (G.induce (S∪T)ᶜ).ConnectedComponent := by
  classical
  let _ := Fintype.ofFinite X
  let P := equalFactorCaps G p
  exact {C | C∈P.originalTightOdd S T ∧ crossCount G (cutPieceSet G (S∪T) C) (S∪T)=0}

/-- Each original tight odd component with a positive boundary uses
at least two different boundary edges in the equal-cap case. -/
theorem equal_factor_cut_le_no_ports {X : Type u} [Finite X] (G : SimpleGraph X) (p : ℕ)
    (cap : ∀x,Nat.card (G.neighborSet x)≤2*p) (S T:Set X) (apart : Disjoint S T) :
    originalFactorCut G p p S T≤((noPortOddPieces G p S T).ncard:ℤ) := by
  classical
  let _ := Fintype.ofFinite X
  let P := equalFactorCaps G p
  let A := S∪T
  let H := G.induce Aᶜ
  let _ := Fintype.ofFinite H.ConnectedComponent
  let B : Set H.ConnectedComponent := P.originalTightOdd S T
  let N : Set H.ConnectedComponent := noPortOddPieces G p S T
  let port (C:H.ConnectedComponent) := crossCount G (cutPieceSet G A C) A
  have caps (x:X) : P.G.degree x≤P.A x+P.B x := by
    change G.degree x≤p+p
    simpa only [Nat.two_mul,Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using cap x
  have parity (C:H.ConnectedComponent) (hc:C∈B) : 2∣port C := by
    have tight := (P.coreTight_iff_degree C caps).1 hc.1
    apply cut_piece_boundary_parity G A C p
    rintro z ⟨v,mem,rfl⟩
    have d := tight ⟨v,mem⟩
    change G.degree v.val=p+p at d
    simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree,Nat.two_mul] using d
  have point (C:H.ConnectedComponent) : (if C∈B then 2 else 0)≤port C+(if C∈N then 2 else 0) := by
    by_cases yes : C∈B
    · have div := parity C yes
      by_cases zero : port C=0
      · have included : C∈N := ⟨yes,zero⟩
        simp [yes,included]
      · split_ifs <;> omega
    · simp [yes]
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun C _ => point C)
  have cnt (K:Set H.ConnectedComponent) : (∑C:H.ConnectedComponent,if C∈K then 2 else 0)=2*K.ncard := by
    calc
      _ = ∑C∈(Finset.univ.filter (fun C:H.ConnectedComponent => C∈K)),2 := (Finset.sum_filter _ _).symm
      _ = 2*K.ncard := by simp [Set.ncard_eq_toFinset_card',Nat.mul_comm]
  rw [Finset.sum_add_distrib,cnt B,cnt N] at total
  have ports := total_cut_piece_boundaries G A
  change (∑C:H.ConnectedComponent,port C)=crossCount G Aᶜ A at ports
  rw [ports] at total
  have fee := balanced_total_boundary G p cap S T apart
  change crossCount G Aᶜ A+2*crossCount G T S≤2*p*S.ncard+2*p*T.ncard at fee
  have full : B.ncard+crossCount G T S≤p*S.ncard+p*T.ncard+N.ncard := by
    simp only [Nat.mul_assoc] at fee;omega
  have cast : (B.ncard:ℤ)+(crossCount G T S:ℤ)≤(p*S.ncard:ℕ)+(p*T.ncard:ℕ)+(N.ncard:ℤ) := by exact_mod_cast full
  change P.cutDeficit S T≤(N.ncard:ℤ)
  unfold JSP452Audit.Padded.Spec.cutDeficit
  rw [actual_factor_cross_edges]
  let _ := Fintype.ofFinite S
  let _ := Fintype.ofFinite T
  change (B.ncard:ℤ)+(crossCount G T S:ℤ)-(∑_v:↥S,p:ℕ)-(∑_v:↥T,p:ℕ)≤(N.ncard:ℤ)
  simp only [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,nsmul_eq_mul]
  simp only [Nat.cast_mul] at cast ⊢
  push_cast at *
  nlinarith only [cast]

#print axioms actual_factor_cross_edges
#print axioms equal_factor_cut_le_no_ports
end JSP452Audit.StarHost