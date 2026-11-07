import ParityAcrossCountedOriginalPieces
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_eight_has_odd_regular_component (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) : 1≤(oddRegularComponents F.G 8).ncard := by
  by_contra! few
  have none : (oddRegularComponents F.G 8).ncard=0 := by omega
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤8 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq eight
  obtain ⟨S,T,dis,fee,tight⟩ := tight_eight_cut_if_no_odd_component F paid eight none
  let A := S∪T
  let B := uniformOddPieces F.G 3 5 S T
  let J := regionCore F.G A B
  let U := A∪J
  obtain ⟨sat,zero,closed⟩ := tight_cut_closes_selected_region F.G cap none S T dis tight
  have roots := (tight_cut_roots_have_full_degree F.G 8 cap S T dis sat).1
  have full (x) (hx:x∈U) : Nat.card (F.G.neighborSet x)=8 := by
    rcases hx with a|j
    · exact roots x a
    · obtain ⟨v,rfl,mem⟩ := j
      exact uniform_tight_piece_full F.G 3 5 cap S T ((F.G.induce Aᶜ).connectedComponentMk v) mem v.val ⟨v,rfl,rfl⟩
  obtain ⟨k,even⟩ := even_order_of_closed_full_region F.G 8 none U closed full
  have off : J⊆Aᶜ := by rintro _ ⟨x,rfl,_⟩;exact x.property
  have apart : Disjoint A J := disjoint_compl_right.mono_right off
  have size : U.ncard=S.ncard+T.ncard+J.ncard := by rw [Set.ncard_union_eq apart,Set.ncard_union_eq dis]
  obtain ⟨m,pc⟩ := counted_piece_parity_sum F.G 3 5 (by decide) S T
  change J.ncard+crossCount F.G J T=2*m+B.ncard at pc
  obtain ⟨n,ct⟩ := closed_cut_target_even_incidence F.G 4 S T J dis off zero (fun x hx => roots x (Or.inr hx))
  rw [uniform_factor_cut_on_original] at fee
  change (B.ncard:ℤ)+(crossCount F.G T S:ℤ)-3*(S.ncard:ℤ)-5*(T.ncard:ℤ)=1 at fee
  omega

#print axioms strict_eight_has_odd_regular_component
end JSP452Audit.StarHost
