import AnExactMaximumDegreeCostAndResidualCapIdentifyTheActualStage
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] (G:SimpleGraph X)

def additionalLabels (S T:Set X) : Set ↥(Sᶜ:Set X) := {x|x.val∈T}
omit [Finite X] in
theorem additional_original_union (S T:Set X) (nest:S⊆T) : outerCut S (additionalLabels S T)=T := by
  ext x;constructor
  · rintro (hs|⟨v,hv,rfl⟩);exact nest hs;exact hv
  · intro ht;by_cases hs:x∈S
    · exact Or.inl hs
    · exact Or.inr ⟨⟨x,hs⟩,ht,rfl⟩

def furtherCutIso (S T:Set X) (nest:S⊆T) :
    (G.induce Sᶜ).induce (additionalLabels S T)ᶜ ≃g G.induce Tᶜ := by
  have e := nestedCutIso G S (additionalLabels S T)
  rwa [additional_original_union S T nest] at e

theorem peak_history_second_stage (D:ℕ) (large:2≤D) :
    let b := peakCountAbove G (D-1)
    let c := peakCountAbove G (D-2)
    let S := peakPrefix G b
    let T := peakPrefix G c
    let W := additionalLabels S T
    b≤c ∧ S.ncard=b ∧ T.ncard=c ∧ W.ncard=c-b ∧
      (G.induce Sᶜ).edgeSet.ncard=(G.induce Tᶜ).edgeSet.ncard+(D-1)*(c-b) ∧
      Nonempty (((G.induce Sᶜ).induce Wᶜ) ≃g G.induce Tᶜ) := by
  intro b c S T W
  have order : b≤c := peak_counts_antitone G (by omega)
  have sub : S⊆T := peak_prefix_nested G order
  have sb := (exact_peak_inventory_cut G (D-1)).1
  have tc := (exact_peak_inventory_cut G (D-2)).1
  change S.ncard=b at sb
  change T.ncard=c at tc
  have count := outerCut_ncard S W
  rw [additional_original_union S T sub,tc,sb] at count
  refine ⟨order,sb,tc,by omega,history_equal_fee_interval G b c (D-1) order ?_,⟨furtherCutIso G S T sub⟩⟩
  intro j lo hi
  have head := (peak_fee_antitone G lo).trans (peak_inventory_spec G (D-1)).2.1
  have low := ((peak_inventory_spec G (D-2)).2.2 j).1 hi
  omega

theorem sum_after_both_deletions {Y:Type u} [Finite Y] (H:SimpleGraph Y) (S:Set X) (T:Set Y) {s t r:ℕ} (n m:ℕ→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀j<s,0<n j) (pm:∀j<t,0<m j) (row:ForcingRow (G⊕g H) s t n m r) :
    ForcingRow (G.induce Sᶜ⊕g H.induce Tᶜ) s t n m (r+S.ncard+T.ncard) := by
  have first := delete_only_from_left_summand G H S n m hn hm pn pm row
  have reverse := forcingRow_of_iso (Iso.sumComm (G:=G.induce Sᶜ) (H:=H)) first
  have second := delete_only_from_left_summand H _ T n m hn hm pn pm reverse
  exact forcingRow_of_iso (Iso.sumComm (G:=H.induce Tᶜ) (H:=G.induce Sᶜ)) second

#print axioms additional_original_union
#print axioms furtherCutIso
#print axioms peak_history_second_stage
#print axioms sum_after_both_deletions
end JSP452Audit.StarHost
