import SingleCutTripleMatching
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- The final large single-part obstruction pays positive reserve by building
an actual matching exposing three independent original labels. -/
theorem single_preferred_positive_reserve (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (many : 3≤I.ncard) (D : ℕ) (six : 6≤D) (par : Even D)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (crit : PerfectAfterEveryDeletion Q)
    (s : OnePreferredPart Q I) (conn : (Q.induce s.preferred).Preconnected)
    (small : NoIndependentTriple (Q.induce s.preferred)) : 1≤baseReserve Q D := by
  classical
  by_contra! fail
  have zero : baseReserve Q D=0 := by omega
  obtain ⟨large,x,bad⟩ := zero_single_part_requires_bad_cut Q I ind largest many D six par reg crit s zero
  obtain ⟨shape⟩ := split_large_bad_single Q I ind largest D six reg s large conn small x bad
  obtain ⟨r,ri,i,hi,ir,a,ha,w,hw,xa,ia,ix,rb,_,unique⟩ :=
    forced_root_and_missing_pair Q I ind largest many D six reg crit zero s conn small x bad shape
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
  obtain ⟨J,jm,holes⟩ := cut_triple_matching Q I s D par six x shape M hm i r hi ri ir a ha rb
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

#print axioms single_preferred_positive_reserve
end JSP452Audit.StarHost
