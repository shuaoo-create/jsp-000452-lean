import SumTheComponentTokensOnTheIdenticalOriginalFactorCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X}

theorem odd_cut_actual_source_degree (p q:ℕ) (odd:Odd (p+q)) (oddP:Odd p)
    (cap:∀v,Nat.card (G.neighborSet v)≤p+q) (S T:Set X) (apart:Disjoint S T) :
    (uniformOddPieces G p q S T).ncard+crossCount G T S≤originalDegreeSum G S := by
  classical
  let B := uniformOddPieces G p q S T
  let C := regionCore G (S∪T) B
  let _ := Fintype.ofFinite B
  have per (i:↥B) : 1≤crossCount G (cutPieceSet G (S∪T) i.val) S := by
    have token := counted_piece_has_odd_source_ports G p q odd oddP cap S T apart i.val i.property
    obtain ⟨j,bill⟩ := token;omega
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,
    ←selected_color_cross_sum] at sum
  change B.ncard≤crossCount G C S at sum
  have split : Disjoint C T := Set.disjoint_left.mpr (by
    rintro x ⟨v,rfl,_⟩ hit;exact v.property (Or.inr hit))
  exact (Nat.add_le_add_right sum _).trans (two_crossing_families_at_root_set G S C T split)

theorem even_cut_actual_degree_sum (p q:ℕ) (even:Even (p+q))
    (cap:∀v,Nat.card (G.neighborSet v)≤p+q) (S T:Set X) (apart:Disjoint S T) :
    2*((uniformOddPieces G p q S T).ncard+crossCount G T S)≤
      originalDegreeSum G S+originalDegreeSum G T+2*(oddRegularComponents G (p+q)).ncard := by
  classical
  let A := S∪T
  let B := uniformOddPieces G p q S T
  let N := portlessUniformPieces G p q S T
  let Q := G.induce Aᶜ
  let _ := Fintype.ofFinite Q.ConnectedComponent
  let port (i:Q.ConnectedComponent) := crossCount G (cutPieceSet G A i) A
  obtain ⟨d,eq⟩ := even
  have per (C:Q.ConnectedComponent) : (if C∈B then 2 else 0)≤port C+(if C∈N then 2 else 0) := by
    by_cases hit:C∈B
    · have parity := cut_piece_boundary_parity G A C d (fun x hx =>
        (uniform_tight_piece_full G p q cap S T C hit x hx).trans (by omega))
      change 2∣port C at parity
      by_cases zero:port C=0
      · have noPort:C∈N := ⟨hit,zero⟩
        simp [hit,noPort]
      · split_ifs <;> omega
    · simp [hit]
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun C _ => per C)
  have cnt (U:Set Q.ConnectedComponent) : (∑C:Q.ConnectedComponent,if C∈U then 2 else 0)=2*U.ncard := by
    calc
      _ = ∑C∈(Finset.univ.filter (fun C:Q.ConnectedComponent => C∈U)),2 := (Finset.sum_filter _ _).symm
      _ = 2*U.ncard := by simp [Set.ncard_eq_toFinset_card',Nat.mul_comm]
  rw [Finset.sum_add_distrib,cnt B,cnt N] at sum
  have ports := total_cut_piece_boundaries G A
  change (∑C:Q.ConnectedComponent,port C)=crossCount G Aᶜ A at ports
  rw [ports,cut_cross_union_right G Aᶜ S T apart] at sum
  have so:Disjoint Aᶜ S := disjoint_compl_left.mono_right Set.subset_union_left
  have to':Disjoint Aᶜ T := disjoint_compl_left.mono_right Set.subset_union_right
  have red := two_crossing_families_at_root_set G S Aᶜ T to'
  have blue := two_crossing_families_at_root_set G T Aᶜ S so
  rw [crossCount_swap G S T] at blue
  have no := portless_uniform_count G p q cap S T
  change N.ncard≤_ at no
  change 2*(B.ncard+_)≤_;omega

#print axioms odd_cut_actual_source_degree
#print axioms even_cut_actual_degree_sum
end JSP452Audit.StarHost
