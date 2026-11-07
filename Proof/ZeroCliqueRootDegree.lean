import SingletonZeroStructure
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The surviving clique's original vertices each have exactly one neighbor
in the original largest independent set, and no neighbor among the holes. -/
theorem zero_clique_root_degrees (Q : SimpleGraph X) (I : Set X) (D : ℕ)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (N : (Q.induce Iᶜ).Subgraph)
    (same : N.verts=zeroMateRegion (Q.induce Iᶜ) N) (size : N.verts.ncard=D)
    (clZ : (Q.induce Iᶜ).IsClique (zeroMateRegion (Q.induce Iᶜ) N)) :
    let Z := Subtype.val '' zeroMateRegion (Q.induce Iᶜ) N
    ∀x∈Z,(Q.neighborSet x ∩ I).ncard=1 ∧ (∀y,Q.Adj x y → y∉Z → y∈I) := by
  intro Z x hx
  have cl : Q.IsClique Z := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ne
    exact clZ ha hb (fun eq => ne (congrArg Subtype.val eq))
  have zsize : Z.ncard=D := by
    change (Subtype.val '' zeroMateRegion (Q.induce Iᶜ) N).ncard=D
    rw [Set.ncard_image_of_injective _ Subtype.val_injective,←same,size]
  have dis {u} (hi : u∈I) : u∉Z := by
    rintro ⟨v,hv,eq⟩
    exact v.property (eq ▸ hi)
  have next (y : X) (adj : Q.Adj x y) (away : y∉Z) : y∈I := by
    by_contra out
    obtain ⟨a,ha,eq⟩ := hx
    let b : ↥(Iᶜ : Set X) := ⟨y,out⟩
    have hole : b∉N.verts := fun h => away ⟨b,same ▸ h,rfl⟩
    obtain ⟨v,edge,none,_⟩ := ha
    apply none b hole
    change Q.Adj a.val y
    rwa [eq]
  have account := clique_external_degree Q Z D cl (fun a _ => reg a) ⟨x,hx⟩
  have equal : Q.neighborSet x∩I=Q.neighborSet x∩Zᶜ := by
    ext y
    exact ⟨fun h => ⟨h.1,dis h.2⟩,fun h => ⟨h.1,next y h.1 h.2⟩⟩
  refine ⟨?_,next⟩
  rw [equal,account,zsize]
  omega

#print axioms zero_clique_root_degrees
end JSP452Audit.StarHost
