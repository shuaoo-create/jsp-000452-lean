import FixedCompleteExteriorRow
import ComponentStarLoad
open private JSP452Audit.StarHost.component_of_star_vertex from ComponentStarLoad
namespace JSP452Audit.StarHost
open SimpleGraph

/-- A numerical packing uses distinct vertex slots in the actual original
components, with each star occupying a single component. -/
def FitsComponentOrders {I X : Type*} (H : SimpleGraph X) (n : I→ℕ) : Prop :=
  ∃ f : Vertices n ↪ X, ∀i j,
    H.connectedComponentMk (f (center n i))=H.connectedComponentMk (f ⟨i,j⟩)

theorem fits_of_actual_copy {I X : Type*} (H : SimpleGraph X) (n : I→ℕ)
    (copy : (forest n).IsContained H) : FitsComponentOrders H n := by
  obtain ⟨f⟩ := copy
  exact ⟨⟨f,f.injective⟩,JSP452Audit.StarHost.component_of_star_vertex H n f⟩

noncomputable def componentBudget {s : ℕ} {X : Type*} [Finite X] (H : SimpleGraph X) (n : Fin s→ℕ) :
    RemovalBudget s := by
  classical
  let opts := Finset.univ.filter (fun T : Finset (Fin s) =>
    T.card≤matchingEdges H ∧ FitsComponentOrders H (fun z:↥T => n z.val))
  refine ⟨opts,∅,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp,?_⟩⟩
  let m (z : ↥(∅ : Finset (Fin s))) := n z.val
  have impossible (z : Vertices m) : False := Finset.notMem_empty _ z.1.property
  exact ⟨⟨fun z => (impossible z).elim,fun z => (impossible z).elim⟩,fun i => (Finset.notMem_empty _ i.property).elim⟩

theorem mem_component_budget {s : ℕ} {X : Type*} [Finite X] (H : SimpleGraph X) (n : Fin s→ℕ) (T : Finset (Fin s)) :
    T∈(componentBudget H n).choices ↔ T.card≤matchingEdges H ∧ FitsComponentOrders H (fun z:↥T => n z.val) := by
  classical
  simp [componentBudget]

theorem component_budget_loss_le {s : ℕ} {X : Type*} [Finite X] (H : SimpleGraph X) (n : Fin s→ℕ) :
    (componentBudget H n).loss≤matchingEdges H := by
  apply Finset.sup_le;intro T h
  exact ((mem_component_budget H n T).mp h).1

private theorem reindex_internal_copy {s i l : ℕ} (hl : i+l≤s) (U : Set (Fin l)) (n : Fin s→ℕ)
    {X : Type*} (H : SimpleGraph X)
    (copy : (forest (fun z:U => n (originalSuffixLabel i l hl z.val))).IsContained H) :
    (forest (fun z:↥(originalRemoved i l hl U) => n z.val)).IsContained H := by
  let T := originalRemoved i l hl U
  have origin (z:↥T) : ∃a:U,originalSuffixLabel i l hl a.val=z.val := by
    obtain ⟨a,h,eq⟩ := Finset.mem_map.mp z.property
    exact ⟨⟨a,(Set.Finite.mem_toFinset _).mp h⟩,eq⟩
  let f : ↥T ↪ U := {
    toFun := fun z => (origin z).choose
    inj' := by
      intro a b eq
      apply Subtype.ext
      exact (origin a).choose_spec.symm.trans ((congrArg (fun z:U => originalSuffixLabel i l hl z.val) eq).trans (origin b).choose_spec) }
  let sub := subforestCopy (fun z:↥T => n z.val) (fun z:U => n (originalSuffixLabel i l hl z.val)) f
    (fun z => by change n z.val≤n (originalSuffixLabel i l hl (origin z).choose.val);rw [(origin z).choose_spec])
  exact (show (forest (fun z:↥T => n z.val)).IsContained _ from ⟨sub⟩).trans copy

theorem component_budget_admits {s : ℕ} {X : Type*} [Finite X] (H : SimpleGraph X)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) : AdmitsInternal (componentBudget H n) n H := by
  classical
  intro i l hl U copy
  let T := originalRemoved i l hl U
  have old := reindex_internal_copy hl U n H copy
  have rank := forest_copy_matching H (fun z:↥T => n z.val) (fun z => pn z.val) old
  exact (mem_component_budget H n T).mpr ⟨by simpa using rank,fits_of_actual_copy H _ old⟩

/-- A single original star fitting one real component order is an
allowed numerical removal even if its required edges need not lie there. -/
theorem component_budget_accepts_singleton {s : ℕ} {X : Type*} [Finite X] (H : SimpleGraph X)
    (n : Fin s→ℕ) (i : Fin s) (c : H.ConnectedComponent) (pos : 0<matchingEdges H)
    (room : n i+1≤Nat.card c.supp) : 1≤(componentBudget H n).loss := by
  classical
  let T : Finset (Fin s) := {i}
  let m (z:↥T) := n z.val
  have hit (z:↥T) : z.val=i := Finset.mem_singleton.mp z.property
  let send : Vertices m ↪ Fin (n i+1) := {
    toFun := fun z => ⟨z.2.val,by simpa only [m,hit z.1] using z.2.isLt⟩
    inj' := by
      rintro ⟨u,a⟩ ⟨v,b⟩ eq
      obtain rfl : u=v := Subtype.ext ((hit u).trans (hit v).symm)
      exact congrArg (Sigma.mk u) (Fin.ext (congrArg (fun z:Fin (n i+1) => z.val) eq)) }
  let _ := Fintype.ofFinite c.supp
  let slots : Fin (n i+1) ↪ c.supp :=
    (Function.Embedding.nonempty_of_card_le (by simpa [Nat.card_eq_fintype_card] using room)).some
  let g := send.trans slots
  have fit : FitsComponentOrders H m := by
    refine ⟨g.trans (Function.Embedding.subtype _),fun z k => ?_⟩
    exact ((c.mem_supp_iff _).mp (g (center m z)).property).trans ((c.mem_supp_iff _).mp (g ⟨z,k⟩).property).symm
  have mem := (mem_component_budget H n T).mpr ⟨by simp [T];omega,fit⟩
  have one := (componentBudget H n).removed_le_loss ⟨T,mem⟩
  simpa [T] using one

#print axioms fits_of_actual_copy
#print axioms component_budget_loss_le
#print axioms component_budget_admits
#print axioms component_budget_accepts_singleton
end JSP452Audit.StarHost
