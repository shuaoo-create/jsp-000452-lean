import FewUnitStars
import ExactPathEvenSplit
open private JSP452Audit.StarHost.rank_component_sides from ComponentSplitColor

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A vertex of a tight barrier costs exactly one matching edge on deletion.
Color its incident edges red. All remaining edges are the blue graph on the
same original host (with the chosen vertex isolated). -/
theorem tight_barrier_vertex_star_coloring {X : Type*} [Finite X] (G : SimpleGraph X)
    (S : Set X) (tight : IsTightBarrier G S) (v : X) (inside : v∈S) :
    ∃R : SimpleGraph X,R≤G ∧ matchingEdges R≤1 ∧ matchingEdges (G \ R)+1=matchingEdges G := by
  let U : Set X := {v}
  let R : SimpleGraph X := {
    Adj a b := G.Adj a b ∧ (a∈U ∨ b∈U)
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
    loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩ }
  have one : U.ncard=1 := Set.ncard_singleton v
  have loss := tight_deletes_rank G S U tight (Set.singleton_subset_iff.mpr inside)
  have red := matchingEdges_le_cover_card R U (fun _ _ h => h.2)
  have separate := JSP452Audit.StarHost.rank_component_sides (G \ R) U (by
    intro a member b _ h
    exact h.2 ⟨h.1,Or.inl member⟩)
  have isolated : (G \ R).induce U=⊥ := by
    ext a b
    exact ⟨fun h => (h.2 ⟨h.1,Or.inl a.property⟩).elim,False.elim⟩
  have rest : (G \ R).induce Uᶜ=G.induce Uᶜ := by
    ext a b
    exact ⟨fun h => h.1,fun h => ⟨h,fun incident => incident.2.elim a.property b.property⟩⟩
  rw [isolated,rest,matchingEdges_bot] at separate
  exact ⟨R,fun _ _ h => h.1,by omega,by omega⟩

/-- If the blue target has exactly as many stars as the original matching
rank, a nonempty tight barrier would give a single red star and a blue
graph of rank one less. Both alternatives miss their positive target. -/
theorem full_rank_forcing_tight_barrier_empty {X : Type*} [Finite X] (G : SimpleGraph X)
    {s t : ℕ} (redLength : 2≤s) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (force : Forces G (forest n) (forest m)) (rank : matchingEdges G=t)
    (S : Set X) (tight : IsTightBarrier G S) : S=∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨v,inside⟩
  obtain ⟨R,sub,red,blue⟩ := tight_barrier_vertex_star_coloring G S tight v inside
  rcases force R sub with copyR|copyB
  · have need := forest_copy_matching R n pn copyR
    rw [Fintype.card_fin] at need
    omega
  · have need := forest_copy_matching (G \ R) m pm copyB
    rw [Fintype.card_fin] at need
    omega

/-- Every individual star is assigned to its original center's component.
A factor-critical component receiving its matching rank in positive stars
has room for at most one extra leaf, even if other components are large. -/
theorem critical_components_rank_saturating_copy_binary {X : Type*} [Finite X]
    (G : SimpleGraph X) {t : ℕ} (m : Fin t→ℕ) (pm : ∀j,1≤m j)
    (copy : (forest m).Copy G) (rank : matchingEdges G=t)
    (critical : ∀c:G.ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph) :
    ∀j,m j≤2 := by
  classical
  intro j
  let c := G.connectedComponentMk (copy (center m j))
  let A : Set (Fin t) := {i | copy (center m i)∈c.supp}
  have charge := (critical_component_star_load G m pm copy
    (show Fintype.card (Fin t)=matchingEdges G by rw [Fintype.card_fin,rank]) c (critical c)).1
  change (∑ᶠ i:A,(m i.val-1))≤1 at charge
  rw [finsum_eq_sum_of_fintype] at charge
  let root : A := ⟨j,rfl⟩
  have term := Finset.single_le_sum (s:=Finset.univ) (f:=fun i:A => m i.val-1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ root)
  change m j-1≤∑i:A,(m i.val-1) at term
  omega

/-- This is an actual forcing-host constraint: with at least two positive
red stars and blue length equal to the matching number, every blue star
must have one or two leaves. No regularity assumption is needed. -/
theorem full_rank_forcing_long_profile_binary {X : Type*} [Finite X] (G : SimpleGraph X)
    {s t : ℕ} (redLength : 2≤s) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (force : Forces G (forest n) (forest m)) (rank : matchingEdges G=t) :
    ∀j,m j≤2 := by
  classical
  obtain ⟨S,tight,parts⟩ := exists_critical_barrier G
  have empty := full_rank_forcing_tight_barrier_empty G redLength n m pn pm force rank S tight
  subst S
  rw [show ((∅ : Set X)ᶜ)=(Set.univ : Set X) by ext; simp] at parts
  let H := G.induce (Set.univ : Set X)
  let e := induceUnivIso G
  have rankH : matchingEdges H=t := (rank_eq_of_graph_iso e).trans rank
  have blue : (forest m).IsContained G := by
    rcases force ⊥ bot_le with impossible|survives
    · have need := forest_copy_matching (⊥ : SimpleGraph X) n pn impossible
      rw [Fintype.card_fin,matchingEdges_bot] at need
      omega
    · simpa only [sdiff_bot] using survives
  obtain ⟨f⟩ := blue.trans e.symm.isContained
  exact critical_components_rank_saturating_copy_binary H m pm f rankH (fun c => (parts c).2)

/-- The original Erdős 561 equality when one side has two stars, for every
positive opposite length and arbitrary positive nonincreasing leaf numbers. -/
theorem erdos561_two_by_arbitrary {t : ℕ} (ht : 0<t)
    (n : Fin 2→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) :
    sizeRamsey (forest n) (forest m)=∑k∈Finset.Icc 2 (2+t),diagonal n m k := by
  by_contra fail
  obtain ⟨V,G,edgeCount,force⟩ := star_min_attained n m
  have row := (finite_targets_row_zero G (by decide : 0<2) ht n m).mpr force
  have upper := erdos561_upper n m
  have strict : G.edgeSet.ncard<rowEnergy n m 0 := by rw [edgeCount,rowEnergy_zero]; omega
  have account := row_energy_budget (by decide : 0<2) ht n m hn hm pn pm G 0 row
  have lower := row_suffix_matching_floor n m pn pm G row 0 0 (by decide) ht rfl
  simp only [Nat.sub_zero] at lower
  have count : rowCount 2 t 0=t+1 := by dsimp [rowCount]; omega
  have rank : matchingEdges G=t := by omega
  have binary := full_rank_forcing_long_profile_binary G (by decide : 2≤2) n m pn pm force rank
  exact fail (erdos561_two_against_binary ht n m hn hm pn pm binary)

/-- Exchange red and blue while retaining the original antidiagonal sum. -/
theorem erdos561_arbitrary_by_two {s : ℕ} (hs : 0<s)
    (n : Fin s→ℕ) (m : Fin 2→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) :
    sizeRamsey (forest n) (forest m)=∑k∈Finset.Icc 2 (s+2),diagonal n m k := by
  apply exact_of_forcing_lower
  intro N G force
  have bound := sizeRamsey_le_of_host _ _ _ (forces_swap force)
  rw [erdos561_two_by_arbitrary hs m n hm hn pm pn] at bound
  simpa only [Nat.add_comm 2 s,diagonal_swap m n] using bound

/-- Uniform terminal for all original inputs in which the shorter side
has at most two stars. Both input lengths remain positive. -/
theorem erdos561_smaller_length_at_most_two {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (small : min s t≤2) :
    sizeRamsey (forest n) (forest m)=∑k∈Finset.Icc 2 (s+t),diagonal n m k := by
  by_cases single : min s t=1
  · exact erdos561_single_list hs ht n m hn hm pn pm single
  have choice : s=2 ∨ t=2 := by omega
  rcases choice with rfl|rfl
  · exact erdos561_two_by_arbitrary ht n m hn hm pn pm
  · exact erdos561_arbitrary_by_two hs n m hn hm pn pm

#print axioms tight_barrier_vertex_star_coloring
#print axioms full_rank_forcing_tight_barrier_empty
#print axioms critical_components_rank_saturating_copy_binary
#print axioms full_rank_forcing_long_profile_binary
#print axioms erdos561_two_by_arbitrary
#print axioms erdos561_arbitrary_by_two
#print axioms erdos561_smaller_length_at_most_two
end JSP452Audit.StarHost

