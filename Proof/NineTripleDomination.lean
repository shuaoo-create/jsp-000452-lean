import UnpaidDensityObstruction
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- In a regular graph on at most 2D+1 vertices every distinct pair is
covered by one closed neighborhood. -/
theorem two_labels_one_center (G : SimpleGraph X) (D : ℕ)
    (reg : ∀x,Nat.card (G.neighborSet x)=D) (order : Nat.card X≤2*D+1)
    (a b : X) (ne : a≠b) :
    ∃z,(a=z ∨ G.Adj a z) ∧ (b=z ∨ G.Adj b z) := by
  classical
  by_cases edge : G.Adj a b
  · exact ⟨a,Or.inl rfl,Or.inr edge.symm⟩
  have da := reg a
  have db := reg b
  rw [Nat.card_coe_set_eq] at da db
  have sub : G.neighborSet a ∪ G.neighborSet b ⊆ ({a,b} : Set X)ᶜ := by
    rintro v (av|bv) (rfl|eq)
    · exact G.loopless.irrefl _ av
    · exact edge ((Set.mem_singleton_iff.mp eq) ▸ av)
    · exact edge bv.symm
    · exact G.loopless.irrefl b ((Set.mem_singleton_iff.mp eq) ▸ bv)
  have common : ¬Disjoint (G.neighborSet a) (G.neighborSet b) := by
    intro dis
    have size := Set.ncard_le_ncard sub
    rw [Set.ncard_union_eq dis,da,db,Set.ncard_compl,Set.ncard_pair ne] at size
    have enough := Set.ncard_le_ncard (Set.subset_univ ({a,b} : Set X))
    rw [Set.ncard_pair ne,Set.ncard_univ] at enough
    omega
  obtain ⟨z,az,bz⟩ := Set.not_disjoint_iff_nonempty_inter.mp common
  exact ⟨z,Or.inr az,Or.inr bz⟩

theorem four_regular_nine_dominating_three (G : SimpleGraph X) (order : Nat.card X=9)
    (reg : ∀x,Nat.card (G.neighborSet x)=4) :
    ∃S : Set X,S.ncard≤3 ∧ ∀v,v∉S → ∃z∈S,G.Adj v z := by
  classical
  have nonempty : Nonempty X := Nat.card_pos_iff.mp (by omega) |>.1
  let x := Classical.choice nonempty
  let U := (insert x (G.neighborSet x))ᶜ
  have deg := reg x
  rw [Nat.card_coe_set_eq] at deg
  have count : U.ncard=4 := by
    dsimp [U]
    rw [Set.ncard_compl,Set.ncard_insert_of_notMem (show x∉G.neighborSet x from G.loopless.irrefl x),deg,order]
  obtain ⟨A,sub,size⟩ := Set.exists_subset_card_eq (s:=U) (show 2≤U.ncard by omega)
  have rest : (U \ A).ncard=2 := by rw [Set.ncard_sdiff sub,count,size]
  obtain ⟨a,b,ab,eA⟩ := Set.ncard_eq_two.mp size
  obtain ⟨c,d,cd,eB⟩ := Set.ncard_eq_two.mp rest
  obtain ⟨p,ap,bp⟩ := two_labels_one_center G 4 reg (by omega) a b ab
  obtain ⟨q,cq,dq⟩ := two_labels_one_center G 4 reg (by omega) c d cd
  let S : Set X := {x,p,q}
  have sx : x∈S := Or.inl rfl
  have sp : p∈S := Or.inr (Or.inl rfl)
  have sq : q∈S := Or.inr (Or.inr rfl)
  have sc : S.ncard≤3 := by
    have h1 := Set.ncard_insert_le x ({p,q} : Set X)
    have h2 := Set.ncard_insert_le p ({q} : Set X)
    rw [Set.ncard_singleton] at h2
    dsimp [S];omega
  refine ⟨S,sc,?_⟩
  intro v hv
  have extract {a z : X} (az : a=z ∨ G.Adj a z) (sz : z∈S) (ev : v=a) : ∃k∈S,G.Adj v k := by
    subst v
    rcases az with eq|edge
    · exact (hv (eq ▸ sz)).elim
    · exact ⟨z,sz,edge⟩
  by_cases vu : v∈U
  · by_cases va : v∈A
    · rw [eA] at va
      rcases va with ev|ev
      · exact extract ap sp ev
      · exact extract bp sp (Set.mem_singleton_iff.mp ev)
    · have vb : v∈U \ A := ⟨vu,va⟩
      rw [eB] at vb
      rcases vb with ev|ev
      · exact extract cq sq ev
      · exact extract dq sq (Set.mem_singleton_iff.mp ev)
  · have inside : v∈insert x (G.neighborSet x) := by
      by_contra no
      exact vu no
    rcases inside with eq|edge
    · exact (hv (eq ▸ sx)).elim
    · exact ⟨x,sx,(show G.Adj x v from edge).symm⟩

#print axioms two_labels_one_center
#print axioms four_regular_nine_dominating_three
end JSP452Audit.StarHost
