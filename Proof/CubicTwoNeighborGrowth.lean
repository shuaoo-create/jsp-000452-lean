import CubicLowComponentLabel
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

def cubicOpen (H : SimpleGraph X) (I:Set X) : Set X := {w | ∃i∈I,H.Adj i w}

theorem cubic_open_insert (H : SimpleGraph X) (I:Set X) (x:X) :
    cubicOpen H (insert x I)=cubicOpen H I∪H.neighborSet x := by
  ext w
  constructor
  · rintro ⟨i,hi,edge⟩
    rcases hi with eq|hi
    · subst i;exact Or.inr edge
    · exact Or.inl ⟨i,hi,edge⟩
  · rintro (⟨i,hi,e⟩|e)
    · exact ⟨i,Set.mem_insert_of_mem _ hi,e⟩
    · exact ⟨x,Set.mem_insert _ _,e⟩

/-- An untouched vertex can be added at cost two: either it shares a
neighbour already counted, or it starts inside a wholly untouched component
at a vertex of degree at most two. -/
theorem cubic_neighbor_extension (H : SimpleGraph X) (cap : ∀v,Nat.card (H.neighborSet v)≤3)
    (low : ∀c:H.ConnectedComponent,∃v∈c.supp,Nat.card (H.neighborSet v)≤2)
    (I:Set X) (ind:H.IsIndepSet I) (space : (I∪cubicOpen H I)ᶜ.Nonempty) :
    ∃x:X,x∉I ∧ H.IsIndepSet (insert x I) ∧ (cubicOpen H (insert x I)).ncard≤(cubicOpen H I).ncard+2 := by
  classical
  let N := cubicOpen H I
  let Z := (I∪N)ᶜ
  have candidate : ∃x∈Z,(∃y∈N,H.Adj x y) ∨ Nat.card (H.neighborSet x)≤2 := by
    by_cases found : ∃x∈Z,∃y∈N,H.Adj x y
    · obtain ⟨x,hx,y,hy,edge⟩ := found
      exact ⟨x,hx,Or.inl ⟨y,hy,edge⟩⟩
    obtain ⟨v,hv⟩ := space
    have closed (x:X) (hx:x∈Z) (y:X) (edge:H.Adj x y) : y∈Z := by
      intro hy
      rcases hy with yi|yn
      · exact hx (Or.inr ⟨y,yi,edge.symm⟩)
      · exact found ⟨x,hx,y,yn,edge⟩
    have inside := cubic_closed_component H Z v hv closed
    obtain ⟨x,hx,small⟩ := low (H.connectedComponentMk v)
    exact ⟨x,inside hx,Or.inr small⟩
  obtain ⟨x,away,why⟩ := candidate
  have fresh : x∉I := fun h => away (Or.inl h)
  have off : x∉N := fun h => away (Or.inr h)
  have next : H.IsIndepSet (insert x I) := by
    apply Set.Pairwise.insert ind
    intro y hy _
    have no : ¬H.Adj x y := fun e => off ⟨y,hy,e.symm⟩
    exact ⟨no,fun e => no e.symm⟩
  refine ⟨x,fresh,next,?_⟩
  rw [cubic_open_insert]
  change (N∪H.neighborSet x).ncard≤N.ncard+2
  rcases why with ⟨y,hy,edge⟩|sm
  · have meet : 0<(N∩H.neighborSet x).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨y,hy,edge⟩
    have eq := Set.ncard_union_add_ncard_inter N (H.neighborSet x)
    have atMost : (H.neighborSet x).ncard≤3 := (Nat.card_coe_set_eq _).symm.le.trans (cap _)
    omega
  · have union := Set.ncard_union_le N (H.neighborSet x)
    rw [Nat.card_coe_set_eq] at sm
    omega

/-- Every requested prefix up to one third of the graph order has a real
independent set with at most twice as many original neighbours. -/
theorem cubic_independent_prefix (H : SimpleGraph X) (cap : ∀v,Nat.card (H.neighborSet v)≤3)
    (low : ∀c:H.ConnectedComponent,∃v∈c.supp,Nat.card (H.neighborSet v)≤2) (j:ℕ)
    (room : 3*j≤Nat.card X) :
    ∃I:Set X,H.IsIndepSet I ∧ I.ncard=j ∧ (cubicOpen H I).ncard≤2*j := by
  classical
  induction j with
  | zero => exact ⟨∅,fun _ h => h.elim,by simp,by simp [cubicOpen]⟩
  | succ j ih =>
    obtain ⟨I,ind,size,used⟩ := ih (by omega)
    have atMost := Set.ncard_union_le I (cubicOpen H I)
    have all := Set.ncard_add_ncard_compl (I∪cubicOpen H I)
    have available : (I∪cubicOpen H I)ᶜ.Nonempty := (Set.ncard_pos (Set.toFinite _)).1 (by omega)
    obtain ⟨x,fresh,next,cost⟩ := cubic_neighbor_extension H cap low I ind available
    exact ⟨insert x I,next,by rw [Set.ncard_insert_of_notMem fresh,size],by omega⟩

#print axioms cubic_neighbor_extension
#print axioms cubic_independent_prefix
end JSP452Audit.StarHost
