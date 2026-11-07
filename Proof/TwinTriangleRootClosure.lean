import TwinTrianglesRankCap
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- Twelve incidences from the two triangles saturate three real roots.
Connectedness then forces these nine labels to exhaust the original graph. -/
theorem three_roots_exhaust_twin_triangles (Q : SimpleGraph X) (I : Set X)
    (h : TwinTriangleParts Q I) (reg : ∀v,Nat.card (Q.neighborSet v)=4) (conn : Q.Connected)
    (few : (triangleRoots Q I h).ncard≤3) :
    triangleRoots Q I h=I ∧ I.ncard=3 ∧ ∀v,v∈I ∨ v∈h.P∪h.C := by
  classical
  let A := h.P∪h.C
  let R := triangleRoots Q I h
  let _ := Fintype.ofFinite R
  have aSize : A.ncard=6 := by rw [show A=h.P∪h.C from rfl,Set.ncard_union_eq h.pc,h.pSize,h.cSize]
  have rsub : R⊆I := fun _ hv => hv.1
  have ext (v:X) (hv:v∈A) : Q.neighborSet v∩R=Q.neighborSet v∩I := by
    ext w
    exact ⟨fun m => ⟨m.1,rsub m.2⟩,fun m => ⟨m.1,m.2,v,hv,m.1⟩⟩
  have degree (v:X) (hv:v∈A) : (Q.neighborSet v∩R).ncard=2 := by
    rw [ext v hv]
    rcases hv with hp|hc
    · exact twin_triangle_two_root_neighbors Q I h.P h.pSize h.pClique h.pOut h.pExt reg v hp
    · exact twin_triangle_two_root_neighbors Q I h.C h.cSize h.cClique h.cOut h.cExt reg v hc
  let f (r:R) := (Q.neighborSet r.val∩A).ncard
  have sum : ∑r:R,f r=12 := by
    have e:=uniform_cross_count Q A R 2 degree
    rw [crossCount_eq_neighbor_sum,aSize] at e
    exact e
  have cap (r:R) : f r≤4 := by
    unfold f
    exact (Set.ncard_le_ncard Set.inter_subset_left).trans ((Nat.card_coe_set_eq _).symm.le.trans (reg r.val).le)
  have upper := Finset.sum_le_sum (s:=(Finset.univ : Finset R)) (fun r _ => cap r)
  have const : (∑_r:R,(4:ℕ))=R.ncard*4 := by simp [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  rw [sum,const] at upper
  change R.ncard≤3 at few
  have size : R.ncard=3 := by omega
  have full (r:R) : f r=4 := by
    by_contra wrong
    have lt := Finset.sum_lt_sum (s:=(Finset.univ : Finset R)) (fun w _ => cap w)
      ⟨r,Finset.mem_univ r,lt_of_le_of_ne (cap r) wrong⟩
    rw [sum,const,size] at lt;omega
  have sat (r:X) (hr:r∈R) : Q.neighborSet r⊆A := by
    have bound : (Q.neighborSet r).ncard≤(Q.neighborSet r∩A).ncard := by
      rw [←Nat.card_coe_set_eq,reg];exact (full ⟨r,hr⟩).symm.le
    have eq := Set.eq_of_subset_of_ncard_le Set.inter_subset_left bound
    intro w hw
    exact (show w∈Q.neighborSet r∩A from eq.symm ▸ hw).2
  have outside : A⊆Iᶜ := Set.union_subset h.pOut h.cOut
  have closed {u v:X} (inK:u∈R∪A) (edge:Q.Adj u v) : v∈R∪A := by
    rcases inK with root|label
    · exact Or.inr (sat u root edge)
    by_cases yes : v∈A
    · exact Or.inr yes
    have vi : v∈I := by
      rcases label with hp|hc
      · exact h.pExt u hp v edge (fun m => yes (Or.inl m))
      · exact h.cExt u hc v edge (fun m => yes (Or.inr m))
    exact Or.inl ⟨vi,u,label,edge⟩
  obtain ⟨a,ha⟩ := (Set.ncard_pos (Set.toFinite A)).mp (by omega)
  have whole (v:X) : v∈R∪A := by
    have reach := (reachable_iff_reflTransGen a v).mp (conn.preconnected a v)
    induction reach with
    | refl => exact Or.inr ha
    | tail _ adj ih => exact closed ih adj
  have eq : R=I := Set.Subset.antisymm rsub (fun v hv => (whole v).resolve_right (fun inA => outside inA hv))
  exact ⟨eq,eq ▸ size,fun v => (whole v).elim (fun hr => Or.inl (rsub hr)) Or.inr⟩

#print axioms three_roots_exhaust_twin_triangles
end JSP452Audit.StarHost
