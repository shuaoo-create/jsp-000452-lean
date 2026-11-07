import SmallSingleFromFour
import CriticalSingleFromFour
import BadSingleCutFromFour
import ForceOneRootFromFour
import TripleMatchingFromFour
import SingleCutTripleMatching
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

theorem zero_single_part_requires_bad_cut_from_four (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (many : 3≤I.ncard) (D : ℕ) (four : 4≤D) (par : Even D)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (crit : PerfectAfterEveryDeletion Q)
    (s : OnePreferredPart Q I) (zero : baseReserve Q D=0) :
    D+1≤s.preferred.ncard ∧ ∃x:s.preferred,¬ExposablePoint (Q.induce s.preferred) x := by
  classical
  have enough : D+1≤s.preferred.ncard := by
    by_contra! short
    have odd := Nat.odd_iff.mp s.odd
    have evenD := Nat.even_iff.mp par
    obtain ⟨U,c,w⟩ := small_single_part_witness_from_four Q I ind many D four par reg s (by omega)
    have bound := deletionBudget_le_of_witness Q (D-1) U w
    have present := (Set.ncard_pos (Set.toFinite I)).mp (by omega)
    have eq := ((zero_reserve_independent_cut Q D (by omega) reg crit zero I present ind).2.2
      (D-1) (by omega) (by omega)).2
    omega
  refine ⟨enough,?_⟩
  by_contra! all
  have paid := large_critical_single_part_pays_from_four Q I ind largest many D four reg crit s enough all
  omega

/-- The final large single-part obstruction pays positive reserve by building
an actual matching exposing three independent original labels. -/
theorem single_preferred_positive_reserve_from_four (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (many : 3≤I.ncard) (D : ℕ) (four : 4≤D) (par : Even D)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (crit : PerfectAfterEveryDeletion Q)
    (s : OnePreferredPart Q I) (conn : (Q.induce s.preferred).Preconnected)
    (small : NoIndependentTriple (Q.induce s.preferred)) : 1≤baseReserve Q D := by
  classical
  by_contra! fail
  have zero : baseReserve Q D=0 := by omega
  obtain ⟨large,x,bad⟩ := zero_single_part_requires_bad_cut_from_four Q I ind largest many D four par reg crit s zero
  obtain ⟨shape⟩ := split_large_bad_single_from_four Q I ind largest D four reg s large conn small x bad
  obtain ⟨r,ri,i,hi,ir,a,ha,w,hw,xa,ia,ix,rb,_,unique⟩ :=
    forced_root_and_missing_pair_from_four Q I ind largest many D four reg crit zero s conn small x bad shape
  obtain ⟨W,wperf⟩ := crit i
  obtain ⟨M,hm,supp,_⟩ := lift_perfect_off_vertex_maximum Q i W wperf
  obtain ⟨u,hu,ui,p,hp,up,only⟩ := single_exit_for_matching Q I ind s i hi M hm supp
  have sub : shape.side⊆s.preferred\{x.val} := shape.parts ▸ Set.subset_union_left
  have odd : Odd (Nat.card s.preferred) := by rw [Nat.card_coe_set_eq];exact s.odd
  let v : s.preferred := ⟨w,(sub hw).1⟩
  have ex := every_other_vertex_exposable _ conn odd small x bad v
    (fun eq => (sub hw).2 (Set.mem_singleton_iff.mpr (congrArg Subtype.val eq)))
  have hit := roots_cover_exposable_points Q D (by omega) reg crit zero M hm i u ui
    (fun edge => ind hi hu ui.symm edge) s.preferred (fun h => s.pOut h hi)
    (fun h => s.pOut h hu) supp p hp up only v ex
  have ur : u=r := hit.elim (fun e => (ir (unique i hi e)).elim) (unique u hu)
  subst u
  obtain ⟨J,jm,holes⟩ := cut_triple_matching_from_four Q I s D par four x shape M hm i r hi ri ir a ha rb
    supp p hp up only
  have indep : Q.IsIndepSet J.vertsᶜ := by
    rw [holes]
    intro y hy z hz diff edge
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy hz
    rcases hy with rfl|rfl|rfl <;> rcases hz with rfl|rfl|rfl <;>
      first | exact diff rfl | exact ix edge | exact ix edge.symm | exact ia edge |
              exact ia edge.symm | exact xa edge | exact xa edge.symm
  have dj : D-1+1=D := by omega
  have biggest := zero_reserve_all_maximal_maximum Q (D-1) (fun y => dj.symm ▸ reg y)
    crit (dj.symm ▸ zero) J jm ((maximal_matching_iff_uncovered_independent Q J jm).mpr indep)
  have paired := matching_vertices_eq_twice_edges jm
  have card := Set.ncard_add_ncard_compl J.verts
  have neqX : i≠x.val := fun eq => s.pOut x.property (eq ▸ hi)
  have neqA : i≠a := fun eq => s.pOut (sub ha).1 (eq ▸ hi)
  have xna : x.val≠a := fun h => shape.off (h.symm ▸ ha)
  rw [holes,Set.ncard_insert_of_notMem (by simp [neqX,neqA]),Set.ncard_pair xna] at card
  have order := factorCritical_order_rank Q crit i
  omega

#print axioms zero_single_part_requires_bad_cut_from_four
#print axioms single_preferred_positive_reserve_from_four
end JSP452Audit.StarHost
