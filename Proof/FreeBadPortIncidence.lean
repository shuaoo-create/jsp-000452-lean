import OddRegionPort

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} [Finite X]

/-- An actual barrier edge at a low port where the good-port condition fails. -/
def badPortIncidence (G : SimpleGraph X) (S : Set X) (D : ℕ) (a : S)
    (c : (G.induce Sᶜ).ConnectedComponent) : Prop :=
  ∃ y : c.supp, y∈portLow c.toSimpleGraph D ∧ ¬GoodPort c.toSimpleGraph y ∧ G.Adj a.val y.val.val

def badFree (G : SimpleGraph X) (S : Set X) (D : ℕ) (A : RootAllocation G S) :
    Set (G.induce Sᶜ).ConnectedComponent :=
  {c ∈ freeFull G S D A | ¬internallyGood c.toSimpleGraph D}

omit [Finite X] in
theorem badPortIncidence_rootIncidence (G : SimpleGraph X) (S : Set X) (D : ℕ)
    (a : S) (c : (G.induce Sᶜ).ConnectedComponent) (hit : badPortIncidence G S D a c) :
    rootIncidence G S a c := by
  obtain ⟨y,_,_,edge⟩ := hit
  exact ⟨y,edge⟩

omit [Finite X] in
theorem badPortIncidence_witness (G : SimpleGraph X) (S : Set X) (D : ℕ)
    (a : S) (c : (G.induce Sᶜ).ConnectedComponent) (hit : badPortIncidence G S D a c) :
    ∃ y : c.supp, y∈portLow c.toSimpleGraph D ∧ G.Adj a.val y.val.val ∧
      ∃ v : c.supp, v≠y ∧ ∃ M : c.toSimpleGraph.Subgraph, M.IsMatching ∧
        M.verts = {w | w≠v} ∧ ∃ z : c.supp, M.Adj y z ∧ ¬c.toSimpleGraph.Adj v z := by
  obtain ⟨y,low,bad,edge⟩ := hit
  exact ⟨y,low,edge,not_good_port_witness c.toSimpleGraph y bad⟩

/-- If every original neighbor avoided S, connectedness would retain all of them
inside the residual component, contradicting the strict internal drop. -/
theorem full_component_low_port_has_root (G : SimpleGraph X) (S : Set X) (D : ℕ)
    (c : (G.induce Sᶜ).ConnectedComponent) (full : allFullComponent G S D c)
    (y : c.supp) (low : y∈portLow c.toSimpleGraph D) :
    ∃ a : S, G.Adj a.val y.val.val := by
  classical
  by_contra missing
  have outside (z : G.neighborSet y.val.val) : z.val∉S :=
    fun hz => missing ⟨⟨z.val,hz⟩,z.property.symm⟩
  let keep (z : G.neighborSet y.val.val) : ↥Sᶜ := ⟨z.val,outside z⟩
  have same (z : G.neighborSet y.val.val) : keep z ∈ c.supp :=
    c.mem_supp_of_adj_mem_supp y.property (show (G.induce Sᶜ).Adj y.val (keep z) from z.property)
  let into (z : G.neighborSet y.val.val) : c.toSimpleGraph.neighborSet y :=
    ⟨⟨keep z,same z⟩,z.property⟩
  have inj : Function.Injective into := fun _ _ eq => Subtype.ext
    (congrArg (fun w : c.toSimpleGraph.neighborSet y => w.val.val.val) eq)
  have count := Nat.card_le_card_of_injective into inj
  rw [full y] at count
  exact (Nat.not_le_of_lt low) count

theorem every_free_bad_has_root (G : SimpleGraph X) (S : Set X) (D : ℕ) (A : RootAllocation G S)
    (c : (G.induce Sᶜ).ConnectedComponent) (hc : c∈badFree G S D A) :
    ∃ a : S, badPortIncidence G S D a c := by
  classical
  have bad := hc.2
  unfold internallyGood at bad
  push Not at bad
  obtain ⟨y,low,fail⟩ := bad
  obtain ⟨a,edge⟩ := full_component_low_port_has_root G S D c hc.1.2 y low
  exact ⟨a,y,low,fail,edge⟩

#print axioms full_component_low_port_has_root
#print axioms every_free_bad_has_root
#print axioms badPortIncidence_witness
end JSP452Audit.StarHost
