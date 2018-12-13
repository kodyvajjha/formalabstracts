import preliminaries
open pfun topological_space set
noncomputable theory
universes u v w

variables {k : ℕ∞} {E : euclidean_space.{u}}

/- topological manifolds -/
structure chart (X : Top) (E : euclidean_space) :=
  (iso : X ≃ₜ. E.to_Top)
  (h1 : is_open iso.to_fun.dom)
  (h2 : is_open iso.inv_fun.dom)

namespace chart
variable {X : Top}
def to_fun (c : chart X E) : X →. E := c.iso.to_fun
def inv_fun (c : chart X E) : E →. X := c.iso.inv_fun
def domain (c : chart X E) : set X := dom c.to_fun
def codomain (c : chart X E) : set E := dom c.inv_fun

def restrict (s : set X) (hs : is_open s) (c : chart X E) : chart (X.restrict s) E :=
⟨(phomeo.restrict_phomeo s).trans c.iso, omitted, omitted⟩

end chart

def compatible_charts {X : Top} (k : ℕ∞) (c₁ c₂ : chart X E) : Prop :=
is_smooth k (c₂.to_fun ∘. c₁.inv_fun) ∧ 
is_smooth k (c₁.to_fun ∘. c₂.inv_fun)

structure topological_manifold (E : euclidean_space) :=
  (carrier : Top)
  (struct2 : t2_space carrier)
  (struct3 : second_countable_topology carrier)
  (charts : set (chart carrier E))
  (cover : ⋃₀ (chart.domain '' charts) = univ)

namespace topological_manifold
instance : has_coe (topological_manifold E) Top :=
⟨topological_manifold.carrier⟩

def restrict (X : topological_manifold E) (s : set X) (hs : is_open s) : 
  topological_manifold E :=
⟨X.carrier.restrict s, omitted, omitted, chart.restrict s hs '' X.charts, omitted⟩ 

end topological_manifold

structure differentiable_manifold (k : ℕ∞) (E : euclidean_space) extends topological_manifold E :=
  (compatible : ∀{{c₁ c₂}}, c₁ ∈ charts → c₂ ∈ charts → compatible_charts k c₁ c₂)


namespace differentiable_manifold

instance : has_coe (differentiable_manifold k E) Top :=
⟨λX, X.to_topological_manifold.carrier⟩

/- a (maximal) atlas is a set of charts which is compatible with all charts of X -/
def atlas (X : differentiable_manifold k E) : set (chart X.carrier E) :=
{ c | ∀c' ∈ X.charts, compatible_charts k c c' }

def restrict (X : differentiable_manifold k E) (s : set X) (hs : is_open s) : 
  differentiable_manifold k E :=
sorry --⟨_, _⟩ 

end differentiable_manifold