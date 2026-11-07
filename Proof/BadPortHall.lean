import HallNeighborhoods

namespace JSP452Audit.StarHost

/-- The bound counts all bad components touching *at least one* root of T.
Choose one actual neighboring root of each bad component; the image T touches
every bad component. One original representative per root yields a partial
injection and discards at most the stated slack. -/
theorem bad_port_partial_assignment {B R : Type*} [Finite B] [Finite R]
    (Inc : B → R → Prop) (η : ℕ)
    (limit : ∀ T : Set R, (rootNeighbors Inc T).ncard ≤ T.ncard + η)
    (touches : ∀ b : B, ∃ r : R, Inc b r) :
    ∃ (selected : Set B) (assign : ↥selected ↪ R),
      (∀ b, Inc b.val (assign b)) ∧ Nat.card B ≤ selected.ncard + η := by
  classical
  choose f edge using touches
  let T := Set.range f
  have covers : rootNeighbors Inc T = Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    exact ⟨f b,Set.mem_range_self b,edge b⟩
  have size := limit T
  rw [covers,Set.ncard_univ] at size
  have witness (r : T) : ∃ b, f b = r.val := r.property
  choose rep hits using witness
  have inj : Function.Injective rep := by
    intro a b eq
    exact Subtype.ext ((hits a).symm.trans ((congrArg f eq).trans (hits b)))
  let selected := Set.range rep
  let assign (b : selected) := f b.val
  have assigns : Function.Injective assign := by
    rintro ⟨a,⟨r,rfl⟩⟩ ⟨b,⟨s,rfl⟩⟩ same
    change f (rep r) = f (rep s) at same
    exact Subtype.ext (congrArg rep (Subtype.ext ((hits r).symm.trans (same.trans (hits s)))))
  have count : selected.ncard=T.ncard :=
    (Set.ncard_range_of_injective inj).trans (Nat.card_coe_set_eq _)
  exact ⟨selected,⟨assign,assigns⟩,fun b => edge b.val,count.symm ▸ size⟩

/-- With |B|=ρ−h and slack ρ−k, the same chosen original components supply
at least k−h pairwise different incident roots. -/
theorem bad_port_assignment_count {B R : Type*} [Finite B] [Finite R]
    (Inc : B → R → Prop) (ρ h k η : ℕ) (hk : k≤ρ) (hh : h≤ρ)
    (count : Nat.card B=ρ-h) (slack : η=ρ-k)
    (limit : ∀ T : Set R, (rootNeighbors Inc T).ncard ≤ T.ncard + η)
    (touches : ∀ b : B, ∃ r : R, Inc b r) :
    ∃ (selected : Set B) (assign : ↥selected ↪ R),
      (∀ b, Inc b.val (assign b)) ∧ Nat.card B ≤ selected.ncard+η ∧ k-h ≤ selected.ncard := by
  obtain ⟨selected,assign,incident,size⟩ := bad_port_partial_assignment Inc η limit touches
  exact ⟨selected,assign,incident,size,by omega⟩

#print axioms bad_port_partial_assignment
#print axioms bad_port_assignment_count
end JSP452Audit.StarHost
