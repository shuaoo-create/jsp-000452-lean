import OneScaledMatchingAttainsTheDeficitAndCoversTheBaselineSlots
import RegularBipartitePick
namespace JSP452Audit.StarHost
universe u v w

theorem remaining_label_degree {E:Type u} {X:Type v} [Finite E] (f:E→X) (A:Set E) (d:ℕ)
    (total:∀x,Nat.card {e // f e=x}=d+1) (one:∀x,Nat.card {e:E // e∈A ∧ f e=x}=1) :
    ∀x,Nat.card {e:↥(Aᶜ:Set E) // f e.val=x}=d := by
  intro x
  let S:Set E := {e|f e=x}
  let T := A∩S
  have sub:T⊆S := Set.inter_subset_right
  have sizes := Set.ncard_sdiff_add_ncard_of_subset sub
  have used : T.ncard=1 := one x
  have nt : S.ncard=d+1 := total x
  let eq : {e:↥(Aᶜ:Set E) // f e.val=x} ≃ ↥(S\T) := {
    toFun := fun e => ⟨e.val.val,e.property,fun t => e.val.property t.1⟩
    invFun := fun e => ⟨⟨e.val,fun a => e.property.2 ⟨a,e.property.1⟩⟩,e.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl}
  have leftover : Nat.card {e:↥(Aᶜ:Set E) // f e.val=x}=(S\T).ncard := Nat.card_congr eq
  omega

private theorem equal_at_single_endpoint {E Y:Type*} (S:Set E) {e f:E} (a:e∈S) (b:f∈S)
    (endpt:E→Y) (ones:∀y,Nat.card {x:E // x∈S ∧ endpt x=y}=1) (eq:endpt e=endpt f) : e=f := by
  obtain ⟨v,alone⟩ := Nat.card_eq_one_iff_exists.mp (ones (endpt f))
  let z : {x:E // x∈S ∧ endpt x=endpt f} := ⟨e,a,eq⟩
  let z' : {x:E // x∈S ∧ endpt x=endpt f} := ⟨f,b,rfl⟩
  exact congrArg Subtype.val ((alone z).trans (alone z').symm)

/-- Every original edge ID appears once, and each colour class is a matching
at both endpoints. Parallel IDs are allowed in the input. -/
theorem colour_regular_edge_ids (k:ℕ) {E:Type u} {A:Type v} {B:Type w} [Finite E] [Finite A] [Finite B]
    (src:E→A) (dst:E→B) (left:∀a,Nat.card {e // src e=a}=k) (right:∀b,Nat.card {e // dst e=b}=k) :
    ∃colour:E→Fin k,∀e f,colour e=colour f → src e=src f ∨ dst e=dst f → e=f := by
  classical
  induction k generalizing E with
  | zero =>
    have empty (e:E) : False := by
      let _ : Nonempty {z // src z=src e} := ⟨⟨e,rfl⟩⟩
      have pos := Nat.card_pos (α:={z // src z=src e});have := left (src e);omega
    exact ⟨fun e => (empty e).elim,fun e => (empty e).elim⟩
  | succ k ih =>
    obtain ⟨S,oneA,oneB⟩ := regular_bipartite_pick src dst (by omega : 0<k+1) left right
    obtain ⟨col,unique⟩ := ih (fun e:↥(Sᶜ:Set E) => src e.val) (fun e => dst e.val)
      (remaining_label_degree src S k left oneA) (remaining_label_degree dst S k right oneB)
    let colour (e:E) : Fin (k+1) := if ok:e∈S then 0 else (col ⟨e,ok⟩).succ
    refine ⟨colour,?_⟩
    intro e f same hit
    by_cases a:e∈S <;> by_cases b:f∈S
    · exact hit.elim (equal_at_single_endpoint S a b src oneA) (equal_at_single_endpoint S a b dst oneB)
    · have no : (0:Fin (k+1))=(col ⟨f,b⟩).succ := by simpa only [colour,dif_pos a,dif_neg b] using same
      exact (Fin.succ_ne_zero _ no.symm).elim
    · have no : (col ⟨e,a⟩).succ=(0:Fin (k+1)) := by simpa only [colour,dif_neg a,dif_pos b] using same
      exact (Fin.succ_ne_zero _ no).elim
    · have same' : col ⟨e,a⟩=col ⟨f,b⟩ := by simpa [colour,a,b] using same
      exact congrArg (fun z:↥(Sᶜ:Set E) => z.val) (unique _ _ same' hit)

#print axioms remaining_label_degree
#print axioms colour_regular_edge_ids
end JSP452Audit.StarHost
