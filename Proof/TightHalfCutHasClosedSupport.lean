import SelectedOriginalCutIncidences
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem tight_cut_closes_selected_region {X:Type u} [Finite X] (G:SimpleGraph X)
    (cap:∀x,Nat.card (G.neighborSet x)≤8) (none:(oddRegularComponents G 8).ncard=0)
    (S T:Set X) (dis:Disjoint S T) (tight:(uniformOddPieces G 3 5 S T).ncard+crossCount G T S=4*S.ncard+4*T.ncard) :
    let A := S∪T
    let B := uniformOddPieces G 3 5 S T
    let J := regionCore G A B
    let U := A∪J
    crossCount G Aᶜ A+2*crossCount G T S=8*S.ncard+8*T.ncard ∧
      crossCount G Uᶜ A=0 ∧ ∀x∈U,∀y,G.Adj x y → y∈U := by
  classical
  intro A B J U
  let _ := Fintype.ofFinite B
  have noPorts := portless_uniform_count G 3 5 cap S T
  rw [show 3+5=8 by decide,none] at noPorts
  have empty : portlessUniformPieces G 3 5 S T=∅ := Set.eq_empty_of_forall_notMem (fun x hx => by
    have pos := (Set.ncard_pos (Set.toFinite _)).mpr (show (portlessUniformPieces G 3 5 S T).Nonempty from ⟨x,hx⟩);omega)
  have fee (c:↥B) : 2≤crossCount G (cutPieceSet G A c.val) A := by
    have div := cut_piece_boundary_parity G A c.val 4 (fun x hx => uniform_tight_piece_full G 3 5 cap S T c.val c.property x hx)
    by_contra! short
    have zero : crossCount G (cutPieceSet G A c.val) A=0 := by omega
    have mem : c.val∈portlessUniformPieces G 3 5 S T := ⟨c.property,zero⟩
    exact (Set.notMem_empty _) (empty ▸ mem)
  have enough := Finset.sum_le_sum (s:=(Finset.univ:Finset B)) (fun c _ => fee c)
  rw [←selected_cut_cross_sum,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id] at enough
  change B.ncard*2≤crossCount G J A at enough
  have off : J⊆Aᶜ := by rintro _ ⟨v,rfl,_⟩;exact v.property
  have eq : J∪Uᶜ=Aᶜ := by
    ext x
    constructor
    · rintro (h|h);exact off h;exact fun a => h (Or.inl a)
    · intro h;by_cases j:x∈J;exact Or.inl j;exact Or.inr (fun ah => ah.elim h j)
  have apart : Disjoint J Uᶜ := disjoint_compl_right.mono_left Set.subset_union_right
  have partition := cut_cross_union_right G A J Uᶜ apart
  rw [eq,crossCount_swap G A Aᶜ,crossCount_swap G A J,crossCount_swap G A Uᶜ] at partition
  have bound := balanced_total_boundary G 4 cap S T dis
  change crossCount G Aᶜ A+2*crossCount G T S≤8*S.ncard+8*T.ncard at bound
  change B.ncard+crossCount G T S=4*S.ncard+4*T.ncard at tight
  have zero : crossCount G Uᶜ A=0 := by omega
  refine ⟨by omega,zero,?_⟩
  intro x hx y e
  rcases hx with a|j
  · by_contra out;exact no_edge_when_port_zero G zero out a e.symm
  · obtain root|inside := regionCore_neighbor G A B j e
    · obtain ⟨v,_,rfl⟩ := root;exact Or.inl v.property
    · exact Or.inr inside

#print axioms tight_cut_closes_selected_region
end JSP452Audit.StarHost
