import SingleSixNoFiveBranchExcluded
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph

def DegreeCutAccount {X:Type*} [Finite X] (G:SimpleGraph X) (d:ℕ) (T:ℕ→Set X) : Prop :=
  (∀j,0<j → j≤d → ∀v,Nat.card ((G.induce (T j)ᶜ).neighborSet v)<j) ∧
    G.edgeSet.ncard=∑i∈Finset.range d,(T (i+1)).ncard

theorem extend_history_by_first_stage {X:Type*} [Finite X] (G:SimpleGraph X) (d:ℕ) (A:Set X)
    (stage:CompleteDegreeStage G (d+1) A) (cap:∀v,Nat.card (G.neighborSet v)≤d+1)
    (S:ℕ→Set ↥(Aᶜ:Set X)) (history:DegreeCutAccount (G.induce Aᶜ) d S) :
    ∃T:ℕ→Set X,T (d+1)=A ∧ DegreeCutAccount G (d+1) T := by
  let T (j:ℕ) := if j=d+1 then A else nestedRemoved A (S j)
  have top : T (d+1)=A := if_pos rfl
  refine ⟨T,top,?_,?_⟩
  · intro j pos high
    by_cases eq:j=d+1
    · subst j;rw [top]
      exact complete_stage_lowers_cap G (d+1) A cap stage
    · have low := history.1 j pos (by omega)
      have cut : T j=nestedRemoved A (S j) := if_neg eq
      have bounded := nested_deletion_cap G A (S j) (j-1) (fun x => by have := low x;omega)
      rw [cut]
      intro v
      have := bounded v
      omega
  · have cost := JSP452Audit.StarHost.degree_on_independent_full_set G A (d+1) stage.2.1 stage.1
    have rest := history.2
    have lower := Finset.sum_congr (s₁:=Finset.range d) rfl (fun i hi =>
      show (T (i+1)).ncard=A.ncard+(S (i+1)).ncard by
        have ne : i+1≠d+1 := by have := Finset.mem_range.mp hi;omega
        rw [show T (i+1)=nestedRemoved A (S (i+1)) from if_neg ne,nested_removed_card])
    rw [Finset.sum_range_succ,top,lower,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] 
    simp only [Nat.cast_id]
    rw [Nat.add_mul] at cost
    omega

theorem complete_degree_cut_account (d:ℕ) : ∀{X:Type u} [Finite X] (G:SimpleGraph X),
    (∀v,Nat.card (G.neighborSet v)≤d) → ∃T:ℕ→Set X,DegreeCutAccount G d T := by
  induction d with
  | zero =>
    intro X _ G cap
    have bot : G=⊥ := by
      ext v w;constructor
      · intro edge
        have pos := (Set.ncard_pos (G.neighborSet v).toFinite).mpr (show (G.neighborSet v).Nonempty from ⟨w,edge⟩)
        have no : (G.neighborSet v).ncard≤0 := cap v
        omega
      · exact False.elim
    refine ⟨fun _ => ∅,fun j pos bound => by omega,?_⟩
    simp [bot]
  | succ d ih =>
    intro X _ G cap
    obtain ⟨A,stage⟩ := complete_degree_stage_exists G (d+1)
    have low := complete_stage_lowers_cap G (d+1) A cap stage
    obtain ⟨S,hist⟩ := ih (G.induce Aᶜ) (fun v => by have := low v;omega)
    obtain ⟨T,_,proof⟩ := extend_history_by_first_stage G d A stage cap S hist
    exact ⟨T,proof⟩

theorem six_column_history_starting_at {X:Type u} [Finite X] (G:SimpleGraph X)
    (cap:∀v,Nat.card (G.neighborSet v)≤6) (B:Set X) (stage:CompleteDegreeStage G 6 B) :
    ∃T:ℕ→Set X,T 6=B ∧ DegreeCutAccount G 6 T := by
  have low := complete_stage_lowers_cap G 6 B cap stage
  obtain ⟨S,hist⟩ := complete_degree_cut_account 5 (G.induce Bᶜ) (fun v => by have := low v;omega)
  exact extend_history_by_first_stage G 5 B stage cap S hist

#print axioms extend_history_by_first_stage
#print axioms complete_degree_cut_account
#print axioms six_column_history_starting_at
end JSP452Audit.StarHost
