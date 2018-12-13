import analysis.real data.pfun
open topological_space set

noncomputable theory
universes u v w
def enat : Type := with_top nat
notation `ℕ∞` := enat

axiom omitted {α : Sort u} : α

variables {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

namespace vector

  def vector_one_equiv : vector α 1 ≃ α  := omitted
end vector

namespace roption

def similar (o₁ o₂ : roption α) : Prop := ∀{{x y}}, x ∈ o₁ → y ∈ o₂ → x = y

namespace similar
  variables {o₁ o₂ o₃ : roption α}
  infix ` =. `:50 := roption.similar
  protected lemma symm (h : o₁ =. o₂) : o₂ =. o₁ := λx y hx hy, (h hy hx).symm
  -- note: it is not transitive, probably good to use different notation
end similar

end roption

namespace pfun

/- continuity of a partial function -/
def is_continuous [topological_space α] [topological_space β] (f : α →. β) := 
continuous (f.as_subtype)

protected def empty (α β : Type*) : α →. β := λx, roption.none
protected def id : α →. α := pfun.lift id
protected def comp (g : β →. γ) (f : α →. β) : α →. γ := λx, roption.bind (f x) g
infix ` ∘. `:90 := pfun.comp

def to_subtype (p : α → Prop) : α →. subtype p := λx, ⟨p x, λ h, ⟨x, h⟩⟩

def similar (f g : α →. β) : Prop := ∀x, f x =. g x

namespace similar
  variables {f g h : α →. β}
  infix ` ~. `:50 := pfun.similar
  protected lemma symm (h : f ~. g) : g ~. f := λx, (h x).symm
  -- note: it is not transitive, probably good to use different notation
end similar

def restrict' (f : α →. β) (p : set α) : α →. β :=
pfun.restrict f (inter_subset_right p (dom f))

def image (f : α →. β) (p : set α) : set β :=
λy, ∃ x (hx : x ∈ dom f), f.fn x hx = y

end pfun

/- a partial equivalence -/
open pfun
structure pequiv (α : Type*) (β : Type*) :=
(to_fun    : α →. β)
(inv_fun   : β →. α)
(dom_inv_fun : ∀{{x}} (hx : x ∈ dom to_fun), to_fun.fn x hx ∈ dom inv_fun)
(dom_to_fun : ∀{{y}} (hy : y ∈ dom inv_fun), inv_fun.fn y hy ∈ dom to_fun)
(left_inv  : inv_fun ∘. to_fun ~. pfun.id)
(right_inv : to_fun ∘. inv_fun ~. pfun.id)

infixr ` ≃. `:25 := pequiv

namespace pequiv

instance : has_coe (α ≃. β) (α →. β) := ⟨pequiv.to_fun⟩
protected def symm (e : α ≃. β) : β ≃. α := 
⟨e.inv_fun, e.to_fun, e.dom_to_fun, e.dom_inv_fun, e.right_inv, e.left_inv⟩
protected def trans (e₁ : α ≃. β) (e₂ : β ≃. γ) : α ≃. γ := 
⟨e₂.to_fun ∘. e₁.to_fun, e₁.inv_fun ∘. e₂.inv_fun, omitted, omitted, omitted, omitted⟩

def restrict' (e : α ≃. β) (p : set α) : α ≃. β :=
⟨e.to_fun.restrict' p, e.inv_fun.restrict' (e.to_fun.image p), omitted, omitted, omitted, omitted⟩

def subtype_pequiv (p : α → Prop) : subtype p ≃. α :=
⟨pfun.lift subtype.val, to_subtype p, omitted, omitted, omitted, omitted⟩

end pequiv

instance [t : topological_space α] : topological_space (vector α n) :=
⨆(l : fin n), induced (λ x, vector.nth x l) t

structure Top :=
  (carrier : Type u)
  (struct : topological_space carrier)

namespace Top

instance : has_coe_to_sort Top := ⟨Type*, Top.carrier⟩
attribute [instance] Top.struct

def restrict (X : Top) (s : set X) : Top := ⟨subtype s, by apply_instance⟩

end Top

structure euclidean_space :=
(carrier : Type u)
(dim : ℕ)
(equiv : carrier ≃ vector ℝ dim)

namespace euclidean_space
instance : has_coe_to_sort euclidean_space := ⟨Type*, euclidean_space.carrier⟩

instance to_topological_space (E : euclidean_space) : 
  topological_space E :=
induced (@euclidean_space.equiv E) (by apply_instance)

def to_Top (E : euclidean_space) : Top :=
⟨E, by apply_instance⟩

instance : has_coe euclidean_space Top :=
⟨to_Top⟩

def real_euclidean_space (n : ℕ) : euclidean_space :=
⟨ℝ, 1, vector.vector_one_equiv.symm⟩

def standard_euclidean_space (n : ℕ) : euclidean_space :=
⟨vector ℝ n, n, equiv.refl _⟩

notation `ℝ^` := standard_euclidean_space
end euclidean_space

variables {k : ℕ∞} {E : euclidean_space.{u}} {E' : euclidean_space.{v}}
def is_smooth_at (k : ℕ∞) (f : E →. E') (x : E) : Prop := omitted
def is_smooth (k : ℕ∞) (f : E →. E') : Prop := omitted --∀x, is_smooth_at k f x

/- the empty map is smooth -/
lemma is_smooth_empty (k : ℕ∞) (E E' : euclidean_space) : is_smooth k (pfun.empty E E') := omitted

/- every smooth map is continuous -/
lemma is_continuous_of_is_smooth {f : E →. E'} (hf : is_smooth k f) : f.is_continuous := 
omitted

/- a partial homeomorphism -/
structure phomeo (X Y : Top) extends X ≃. Y :=
(continuous_to_fun  : to_fun.is_continuous)
(continuous_inv_fun : inv_fun.is_continuous)

infixr ` ≃ₜ. `:25 := phomeo

namespace phomeo
variables {X : Top} {Y : Top} {Z : Top}
def restrict_phomeo (p : set X) : X.restrict p ≃ₜ. X :=
⟨pequiv.subtype_pequiv p, omitted, omitted⟩

def symm (f : X ≃ₜ. Y) : Y ≃ₜ. X := ⟨f.to_pequiv.symm, f.continuous_inv_fun, f.continuous_to_fun⟩
def trans (f : X ≃ₜ. Y) (g : Y ≃ₜ. Z) : X ≃ₜ. Z := ⟨f.to_pequiv.trans g.to_pequiv, omitted, omitted⟩

end phomeo