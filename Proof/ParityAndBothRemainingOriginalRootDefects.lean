import TenDegreeHandshakeOnTheCountedSupport
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
namespace TenOuterCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem roots_full_of_zero_loss (cap:∀x,Nat.card (G.neighborSet x)≤10) (left:K.rootDefect K.S=0)
    (right:K.rootDefect K.T=0) : ∀x∈K.roots,Nat.card (G.neighborSet x)=10 := by
  have each (A:Set X) (loss:K.rootDefect A=0) := degrees_full_at_saturated_sum G 10 A
    (fun x _ => cap x) (by
      have lim := degree_sum_le_cap G A 10 (fun x _ => cap x)
      change 10*A.ncard-originalDegreeSum G A=0 at loss
      omega)
  exact fun x h => h.elim (each K.S left x) (each K.T right x)

theorem parity_if_closed_full (cap:∀x,Nat.card (G.neighborSet x)≤10)
    (none:(oddRegularComponents G 10).ncard=0) (left:K.rootDefect K.S=0) (right:K.rootDefect K.T=0)
    (zero:crossCount G K.supportᶜ K.roots=0) : Even K.score := by
  have roots := K.roots_full_of_zero_loss cap left right
  have full (x) (hx:x∈K.support) : Nat.card (G.neighborSet x)=10 := hx.elim (roots x) (K.core_is_full cap x)
  obtain ⟨k,even⟩ := even_order_of_closed_full_region G 10 none K.support (K.support_closed_of_no_external_root_edge zero) full
  have apart : Disjoint K.roots K.core := disjoint_compl_right.mono_right K.core_outside
  have size : K.support.ncard=K.S.ncard+K.T.ncard+K.core.ncard := by
    change (K.roots∪K.core).ncard=_;rw [Set.ncard_union_eq apart,Set.ncard_union_eq K.apart]
  obtain ⟨m,pc⟩ := counted_piece_parity_sum G 3 7 (by decide) K.S K.T
  change K.core.ncard+crossCount G K.core K.T=2*m+K.pieces.ncard at pc
  obtain ⟨n,ct⟩ := closed_cut_target_even_incidence G 5 K.S K.T K.core K.apart K.core_outside zero
    (fun x hx => roots x (Or.inr hx))
  have fee := K.actual
  rw [uniform_factor_cut_on_original] at fee
  change (K.pieces.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-3*(K.S.ncard:ℤ)-7*(K.T.ncard:ℤ)=(K.score:ℤ) at fee
  rw [Nat.even_iff];omega

theorem exact_root_and_port_losses (cap:∀x,Nat.card (G.neighborSet x)≤10)
    (none:(oddRegularComponents G 10).ncard=0) :
    (G.induce K.S).edgeSet.ncard=0 ∧ (G.induce K.T).edgeSet.ncard=0 ∧ K.excessPairs=0 ∧
    K.rootDefect K.S+K.rootDefect K.T+crossCount G K.supportᶜ K.roots+2*K.score=4 := by
  have ledger := K.exact_handshake cap none
  have pos := K.positive
  have small := K.small
  have guard (one:K.score=1) : 0<K.rootDefect K.S+K.rootDefect K.T+crossCount G K.supportᶜ K.roots := by
    by_contra! no
    obtain ⟨n,even⟩ := K.parity_if_closed_full cap none (by omega) (by omega) (by omega)
    omega
  by_cases one:K.score=1
  · have charge := guard one
    omega
  · omega

theorem each_has_two_ports (cap:∀x,Nat.card (G.neighborSet x)≤10) (none:(oddRegularComponents G 10).ncard=0)
    (C:↥K.pieces) : K.port C=2 := by
  classical
  let _ := Fintype.ofFinite K.pieces
  obtain ⟨pos,even⟩ := K.port_size cap none C
  have clean := (K.exact_root_and_port_losses cap none).2.2.1
  have member := Finset.single_le_sum (f:=fun C:↥K.pieces => (K.port C-2)/2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ C)
  change (K.port C-2)/2≤K.excessPairs at member
  omega

#print axioms parity_if_closed_full
#print axioms exact_root_and_port_losses
#print axioms each_has_two_ports
end TenOuterCut
end JSP452Audit.StarHost
