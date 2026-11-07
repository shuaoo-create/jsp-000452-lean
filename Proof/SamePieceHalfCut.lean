import ActualPortlessUniformPieces
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem half_cut_for_same_pieces {X:Type u} [Finite X] (G:SimpleGraph X) (p a b:ℕ) (sum:a+b=2*p)
    (cap:∀v,Nat.card (G.neighborSet v)≤2*p) (S T:Set X) (apart:Disjoint S T) :
    (uniformOddPieces G a b S T).ncard+crossCount G T S≤p*S.ncard+p*T.ncard+(oddRegularComponents G (2*p)).ncard := by
  classical
  let A := S∪T
  let H := G.induce Aᶜ
  let _ := Fintype.ofFinite H.ConnectedComponent
  let B := uniformOddPieces G a b S T
  let N := portlessUniformPieces G a b S T
  let port (C:H.ConnectedComponent) := crossCount G (cutPieceSet G A C) A
  have localCap (x:X) : Nat.card (G.neighborSet x)≤a+b := (cap x).trans_eq sum.symm
  have parity (C:H.ConnectedComponent) (hc:C∈B) : 2∣port C := by
    apply cut_piece_boundary_parity G A C p
    intro x hx;exact (uniform_tight_piece_full G a b localCap S T C hc x hx).trans sum
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
  have uncut := portless_uniform_count G a b localCap S T
  rw [sum] at uncut
  change N.ncard≤(oddRegularComponents G (2*p)).ncard at uncut
  exact full.trans (Nat.add_le_add_left uncut _)

#print axioms half_cut_for_same_pieces
end JSP452Audit.StarHost
