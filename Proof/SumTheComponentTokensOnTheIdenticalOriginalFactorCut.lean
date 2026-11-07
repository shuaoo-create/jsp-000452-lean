import AnActualOddCutPieceNeedsAnEdgeOrAnExposedOriginalLabel
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X}
theorem two_crossing_families_at_root_set (Y:SimpleGraph X) (S A B:Set X) (apart:Disjoint A B) :
    crossCount Y A S+crossCount Y B S≤originalDegreeSum Y S := by
  rw [crossCount_swap Y A S,crossCount_swap Y B S,←cut_cross_union_right Y S A B apart]
  exact cross_le_original_degree_sum Y S _

theorem layer_tokens_on_one_factor_cut {p q:ℕ} (odd:Odd p) (cap:∀v,Nat.card (G.neighborSet v)≤p+q)
    (S T:Set X) (apart:Disjoint S T) (R:SimpleGraph X) (sub:R≤G) (miss:Set X)
    (degrees:∀x,Nat.card (G.neighborSet x)=p+q →
      (x∈miss → Nat.card (R.neighborSet x)=0) ∧ (x∉miss → Nat.card (R.neighborSet x)=1)) :
    (uniformOddPieces G p q S T).ncard+crossCount G T S≤
      originalDegreeSum R S+originalDegreeSum (G \ R) T+(miss\(S∪T)).ncard := by
  classical
  let B := uniformOddPieces G p q S T
  let _ := Fintype.ofFinite ↥B
  let C := regionCore G (S∪T) B
  let set (i:↥B) := cutPieceSet G (S∪T) i.val
  have per (i:↥B) : 1≤crossCount R (set i) S+crossCount (G \ R) (set i) T+((set i)∩miss).ncard := by
    obtain ⟨n,eq⟩ := actual_cut_piece_needs_layer_token odd cap S T apart i.val i.property R sub miss degrees
    change crossCount R (set i) S+crossCount (G \ R) (set i) T+((set i)∩miss).ncard=2*n+1 at eq;omega
  have bill := Finset.sum_le_sum (s:=(Finset.univ:Finset ↥B)) (fun i _ => per i)
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,
    Finset.sum_add_distrib,Finset.sum_add_distrib] at bill
  have red := selected_color_cross_sum G R (S∪T) B S
  have blue := selected_color_cross_sum G (G \ R) (S∪T) B T
  have missed := selected_piece_intersections G (S∪T) B miss
  change crossCount R C S=∑i:↥B,crossCount R (set i) S at red
  change crossCount (G \ R) C T=∑i:↥B,crossCount (G \ R) (set i) T at blue
  change (C∩miss).ncard=∑i:↥B,((set i)∩miss).ncard at missed
  rw [←red,←blue,←missed] at bill
  change B.ncard≤_ at bill
  have away:C⊆(S∪T)ᶜ := by rintro _ ⟨z,rfl,_⟩;exact z.property
  have sc : Disjoint C S := Set.disjoint_left.mpr (fun _ cm sm => away cm (Or.inl sm))
  have tc : Disjoint C T := Set.disjoint_left.mpr (fun _ cm tm => away cm (Or.inr tm))
  have small := Set.ncard_le_ncard (show C∩miss⊆miss\(S∪T) from fun _ m => ⟨m.2,away m.1⟩)
  have r := two_crossing_families_at_root_set R S C T tc
  have b := two_crossing_families_at_root_set (G \ R) T C S sc
  rw [crossCount_swap (G \ R) S T] at b
  have split := cross_count_color_partition G R sub T S
  change B.ncard+_≤_;omega

#print axioms two_crossing_families_at_root_set
#print axioms layer_tokens_on_one_factor_cut
end JSP452Audit.StarHost
