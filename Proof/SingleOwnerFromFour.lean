import SingleRootOwnerObstruction
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem odd_closed_away_at_four (Q : SimpleGraph X) (crit : PerfectAfterEveryDeletion Q)
    (z : X) (K : Set X) (odd : Odd K.ncard) (zt : z∉K)
    (closed : ∀a∈K,∀b,Q.Adj a b → b=z ∨ b∈K) : False := by
  obtain ⟨P,perf⟩ := crit z
  obtain ⟨M,hm,supp,_⟩ := lift_perfect_off_vertex_maximum Q z P perf
  have matchK : (M.induce K).IsMatching := by
    intro a ha
    have av : a∈M.verts := by rw [supp];exact fun eq => zt (eq ▸ ha)
    obtain ⟨b,ab,only⟩ := hm av
    have bv := M.edge_vert ab.symm
    rw [supp] at bv
    have bk := (closed a ha b (M.adj_sub ab)).resolve_left bv
    exact ⟨b,⟨ha,bk,ab⟩,fun w e => only w e.2.2⟩
  have even := matching_vertices_eq_twice_edges matchK
  change K.ncard=2*(M.induce K).edgeSet.ncard at even
  have parity := Nat.odd_iff.mp odd
  omega

/-- A single owner of D ordinary vertices is saturated. After the sole
two-neighbour vertex is deleted, that owner and the D ordinary vertices
form an isolated odd set, contradicting factor-criticality. -/
theorem single_root_profile_impossible_from_four (Q : SimpleGraph X) (I P : Set X)
    (D : ℕ) (four : 4≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (outside : P⊆Iᶜ)
    (ext : ∀a∈P,∀b,Q.Adj a b → b∉P → b∈I)
    (many : 3≤I.ncard) (size : P.ncard=D+1)
    (pairs : ∀i∈I,∃u∈I,∀v∈P,Q.Adj i v ∨ Q.Adj u v)
    (z:P) (single : ∀v:P,v≠z → (Q.neighborSet v.val∩I).ncard=1) : False := by
  classical
  let A := P\{z.val}
  have aSize : A.ncard=D := by
    have n:=Set.ncard_sdiff_singleton_add_one z.property
    change (P\{z.val}).ncard=D; omega
  have unique (v:A) : ∃! i : I,Q.Adj v.val i.val := by
    let w : P := ⟨v.val,v.property.1⟩
    have ne : w≠z := fun eq => v.property.2 (Set.mem_singleton_iff.mpr (congrArg Subtype.val eq))
    have h := single w ne
    obtain ⟨i,ai,ii⟩ := (Set.ncard_pos (Set.toFinite _)).mp
      (show 0<(Q.neighborSet w.val∩I).ncard by omega)
    refine ⟨⟨i,ii⟩,ai,?_⟩
    intro j aj
    exact Subtype.ext ((Set.ncard_le_one (Set.toFinite _)).mp h.le j.val ⟨aj,j.property⟩ i ⟨ai,ii⟩)
  let owner (v:A) : I := (unique v).choose
  have owns (v:A) : Q.Adj v.val (owner v).val := (unique v).choose_spec.1
  have alone (v:A) (j:I) (adj:Q.Adj v.val j.val) : j=owner v := (unique v).choose_spec.2 j adj
  have pair (i:I) : ∃u:I,∀v,owner v=i ∨ owner v=u := by
    obtain ⟨u,ui,hit⟩ := pairs i.val i.property
    refine ⟨⟨u,ui⟩,?_⟩
    intro v
    rcases hit v.val v.property.1 with hi|hu
    · exact Or.inl (alone v i hi.symm).symm
    · exact Or.inr (alone v ⟨u,ui⟩ hu.symm).symm
  have same := single_owners_coincide (by simpa only [Nat.card_coe_set_eq] using many) owner pair
  obtain ⟨v,hv⟩ := (Set.ncard_pos (Set.toFinite A)).mp (by omega)
  let r := owner ⟨v,hv⟩
  have allRoot (v:A) : Q.Adj r.val v.val := by
    exact (show owner v=r from same v ⟨_,hv⟩) ▸ (owns v).symm
  have rootNeighbors : Q.neighborSet r.val=A := by
    symm
    apply Set.eq_of_subset_of_ncard_le (fun v h => allRoot ⟨v,h⟩)
    change (Q.neighborSet r.val).ncard≤A.ncard
    rw [←Nat.card_coe_set_eq (Q.neighborSet r.val),reg,aSize]
  let K := insert r.val A
  have rout : r.val∉P := fun hp => outside hp r.property
  have rA : r.val∉A := fun h => rout h.1
  have ksize : K.ncard=D+1 := by
    rw [show K=insert r.val A from rfl,Set.ncard_insert_of_notMem rA,aSize]
  have kOdd : Odd K.ncard := ksize.symm ▸ Even.add_one par
  have zk : z.val∉K := by
    rintro (eq|h)
    · exact rout (eq ▸ z.property)
    · exact h.2 (by simp)
  apply odd_closed_away_at_four Q crit z.val K kOdd zk
  intro a ha b edge
  rcases ha with eq|inA
  · have nb : b∈Q.neighborSet r.val := eq ▸ edge
    exact Or.inr (Or.inr (rootNeighbors ▸ nb))
  by_cases bz : b=z.val
  · exact Or.inl bz
  by_cases bp : b∈P
  · exact Or.inr (Or.inr ⟨bp,by simpa using bz⟩)
  have bi := ext a inA.1 b edge bp
  have br : (⟨b,bi⟩:I)=r := (alone ⟨a,inA⟩ ⟨b,bi⟩ edge).trans (same ⟨a,inA⟩ ⟨_,hv⟩)
  exact Or.inr (Or.inl (congrArg Subtype.val br))

#print axioms single_root_profile_impossible_from_four
end JSP452Audit.StarHost
