import ShortListDescent
import SavingComponentColoring
import UniformVsForest

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Keep both input lists and choose their minimum-edge forcing host.
For a shorter length of two, every immediate vertex deletion pays row one
on those same lists. A strict original formula therefore forces this host
to have full degree D, matching number t, and a genuinely unpaid regular
factor-critical component in it. -/
theorem two_list_fixed_component_source {t : ℕ} (ht : 2≤t)
    (n : Fin 2 → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑ k∈Finset.Icc 2 (2+t),diagonal n m k) :
    let D := diagonal n m 2-1
    ∃ (V : ℕ) (G : SimpleGraph (Fin V)),
      G.edgeSet.ncard=sizeRamsey (forest n) (forest m) ∧ Forces G (forest n) (forest m) ∧
      matchingEdges G=t ∧ (∀x,Nat.card (G.neighborSet x)≤D) ∧ 4≤D ∧ Even D ∧
      ∃ c : G.ConnectedComponent, envelopeReserve c.toSimpleGraph D<minimumExposure c.toSimpleGraph D ∧
        (∀x:c.supp,Nat.card (c.toSimpleGraph.neighborSet x)=D) ∧
        PerfectAfterEveryDeletion c.toSimpleGraph := by
  classical
  intro D
  obtain ⟨even,large,first,_⟩ := two_list_failure_width_obstruction (s:=2) (t:=t)
    (by decide) (by omega) n m hn hm pn pm (by omega) fail
  change Even D at even
  change 4≤D at large
  obtain ⟨V,G,edgeCount,force⟩ := star_min_attained n m
  have row := (finite_targets_row_zero G (by decide : 0<2) (by omega : 0<t) n m).mpr force
  have bound := erdos561_upper n m
  have strict : G.edgeSet.ncard<rowEnergy n m 0 := by rw [edgeCount,rowEnergy_zero]; omega
  have child (v : Fin V) : rowEnergy n m 1≤(G.induce {x | x≠v}).edgeSet.ncard := by
    have next := row_delete_one G v _ _ (pad_antitone n hn) (pad_antitone m hm)
      (pad_positive n pn) (pad_positive m pm) row
    by_contra! deficient
    have range := strict_row_range (s:=2) (t:=t) (by decide) (by omega) n m hn hm pn pm
      (G.induce {x | x≠v}) 1 next deficient
    omega
  obtain ⟨rank,paid,under,cap,_,_⟩ := strict_local_normal (s:=2) (t:=t)
    (by decide) (by omega) n m hn hm pn pm G 0 row strict child
  change ∀x,Nat.card (G.neighborSet x)≤D at cap
  have count : rowCount 2 t 0=t+1 := by dsimp [rowCount]; omega
  have minRank := row_suffix_matching_floor n m pn pm G row 0 0 (by decide) (by omega) rfl
  simp only [Nat.sub_zero] at minRank
  have rankG : matchingEdges G=t := by omega
  have height : diagonal n m 2≤D+1 := by dsimp [D]; omega
  have account := row_envelope_reserve (s:=2) (t:=t) (by decide) (by omega) n m hn hm pn pm
    G 0 D row height
  have zero : envelopeReserve G D=0 := by omega
  obtain ⟨_,priced⟩ := row_minimum_exposure (s:=2) (t:=t) (by decide) (by omega) n m hn hm pn pm
    G 0 (by omega) row cap
  change highestWidth n m 0≤minimumExposure G D at priced
  obtain ⟨c,miss⟩ := exists_unpaid_original_component G D D (by omega)
  obtain ⟨reg,crit,_,_,_⟩ := unpaid_component_obstruction G D D (by omega) cap c miss
  exact ⟨V,G,edgeCount,force,rankG,cap,large,even,c,miss,
    fun x => (component_degree_eq G c x).trans (reg x),crit⟩

/-- With two arbitrary positive stars on one side and stars of at most
two leaves on the other, the original antidiagonal formula holds for
every positive opposite length, including all-matchings targets. -/
theorem erdos561_two_against_binary {t : ℕ} (ht : 0<t)
    (n : Fin 2 → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (binary : ∀j,m j≤2) :
    sizeRamsey (forest n) (forest m)=∑ k∈Finset.Icc 2 (2+t),diagonal n m k := by
  by_cases single : t=1
  · exact erdos561_single_list (by decide) ht n m hn hm pn pm (by omega)
  have two : 2≤t := by omega
  by_contra fail
  obtain ⟨V,G,_,force,rankG,cap,four,even,c,_,regular,crit⟩ :=
    two_list_fixed_component_source two n m hn hm pn pm fail
  let D := diagonal n m 2-1
  obtain ⟨R,sub,redCap,blueRank⟩ := saving_component_coloring G D cap c four regular crit even
  have top : diagonal n m 2=n 0+m ⟨0,ht⟩-1 := by
    obtain ⟨i,j,index,eq⟩ := diagonal_attained n m (by decide) ht 0 (by omega)
    have i0 : i=0 := Fin.ext (by change i.val=0; omega)
    have j0 : j=⟨0,ht⟩ := Fin.ext (by change j.val=0; omega)
    simpa only [i0,j0,Nat.zero_add] using eq
  have redLimit : D≤n 0 := by
    have m0 := binary ⟨0,ht⟩
    dsimp [D]; omega
  rcases force R sub with red|blue
  · obtain ⟨v,needed⟩ := high_degree_of_star ((oneStar_in_forest n 0).trans red)
    have upper := redCap v
    change 4≤D at four
    omega
  · have needed := forest_copy_matching (G \ R) m pm blue
    rw [Fintype.card_fin] at needed
    omega

/-- The symmetric orientation preserves the same original lists and sizes. -/
theorem erdos561_binary_against_two {s : ℕ} (hs : 0<s)
    (n : Fin s → ℕ) (m : Fin 2 → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (binary : ∀i,n i≤2) :
    sizeRamsey (forest n) (forest m)=∑ k∈Finset.Icc 2 (s+2),diagonal n m k := by
  apply exact_of_forcing_lower
  intro N G force
  have lower := sizeRamsey_le_of_host _ _ _ (forces_swap force)
  rw [erdos561_two_against_binary hs m n hm hn pm pn binary] at lower
  simpa only [Nat.add_comm 2 s,diagonal_swap m n] using lower

#print axioms erdos561_two_against_binary
#print axioms erdos561_binary_against_two
#print axioms two_list_fixed_component_source
end JSP452Audit.StarHost

