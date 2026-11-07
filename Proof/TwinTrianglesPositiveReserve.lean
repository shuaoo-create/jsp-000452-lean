import TwinTriangleRootClosure
import DominatingPairReserve
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

theorem twin_triangles_positive_reserve (Q : SimpleGraph X) (I : Set X)
    (h : TwinTriangleParts Q I) (ind : Q.IsIndepSet I) (reg : ∀v,Nat.card (Q.neighborSet v)=4)
    (conn : Q.Connected) (crit : PerfectAfterEveryDeletion Q) : 1≤baseReserve Q 4 := by
  classical
  by_contra! unpaid
  have zero : baseReserve Q 4=0 := by omega
  have few := twin_triangles_touch_at_most_three_roots Q I h reg crit zero
  obtain ⟨allRoots,three,cover⟩ := three_roots_exhaust_twin_triangles Q I h reg conn few
  let A := h.P∪h.C
  have degree (v:X) (hv:v∈A) : (Q.neighborSet v∩I).ncard=2 := by
    rcases hv with hp|hc
    · exact twin_triangle_two_root_neighbors Q I h.P h.pSize h.pClique h.pOut h.pExt reg v hp
    · exact twin_triangle_two_root_neighbors Q I h.C h.cSize h.cClique h.cOut h.cExt reg v hc
  have omitRoot (v:X) (hv:v∈A) : ∃r∈I, ¬Q.Adj v r ∧ ∀z∈I, ¬Q.Adj v z → z=r := by
    let M := I\(Q.neighborSet v∩I)
    have count := Set.ncard_sdiff_add_ncard_of_subset (show Q.neighborSet v∩I⊆I from Set.inter_subset_right)
    have size : M.ncard=1 := by change M.ncard+(Q.neighborSet v∩I).ncard=I.ncard at count;rw [three,degree v hv] at count;omega
    obtain ⟨r,hr⟩ := (Set.ncard_pos (Set.toFinite M)).mp (by omega)
    refine ⟨r,hr.1,fun e => hr.2 ⟨e,hr.1⟩,?_⟩
    intro z hz no
    exact (Set.ncard_le_one (Set.toFinite M)).mp size.le z ⟨hz,fun edge => no edge.1⟩ r hr
  have jointly : ∃p∈h.P,∃c∈h.C,∀r∈I,Q.Adj p r ∨ Q.Adj c r := by
    by_contra! no
    obtain ⟨p,hp⟩ := (Set.ncard_pos (Set.toFinite h.P)).mp (by rw [h.pSize];decide)
    obtain ⟨c,hc⟩ := (Set.ncard_pos (Set.toFinite h.C)).mp (by rw [h.cSize];decide)
    obtain ⟨r,ri,_,pr⟩ := omitRoot p (Or.inl hp)
    have cMiss (v:X) (hv:v∈h.C) : ¬Q.Adj v r := by
      obtain ⟨z,zi,zp,zv⟩ := no p hp v hv
      exact pr z zi zp ▸ zv
    obtain ⟨t,_,_,ct⟩ := omitRoot c (Or.inr hc)
    have rt := ct r ri (cMiss c hc)
    have pMiss (v:X) (hv:v∈h.P) : ¬Q.Adj v r := by
      obtain ⟨z,zi,zv,zc⟩ := no v hv c hc
      exact (ct z zi zc).trans rt.symm ▸ zv
    obtain ⟨_,v,hv,hit⟩ := (show r∈triangleRoots Q I h from allRoots.symm ▸ ri)
    exact hv.elim (fun vp => pMiss v vp hit) (fun vc => cMiss v vc hit)
  obtain ⟨p,hp,c,hc,adj⟩ := jointly
  have paid := regular_dominating_pair_base_reserve Q 4 4 (by decide) reg crit I three ind p c
    (h.pc.ne_of_mem hp hc) (by
      intro v vp vc
      rcases cover v with vi|hp'|hc'
      · exact (adj v vi).elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)
      · exact Or.inl (h.pClique hp' hp vp)
      · exact Or.inr (h.cClique hc' hc vc))
  omega

#print axioms twin_triangles_positive_reserve
end JSP452Audit.StarHost
