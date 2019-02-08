import .basic .monster .presentation .suzuki .higman_sims .mclaughlin .conway_groups .mathieu_group
noncomputable theory
open monster suzuki higman_sims mclaughlin conway_groups mathieu_group is_monoid_action coxeter_vertices
open category_theory (mk_ob)
local infix ` ≅ `:60 := isomorphic 
local notation `⟪`:50 a `⟫`:50 := free_group.of a
local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/- the first happy family, a.k.a. Mathieu groups -/

/-- The group $M_{11}$ is the stabilizer of an arbitrary point of the steiner system $S(5,6,12)$ 
  under the evaluation action of its Automorphism group.-/
def M11 : Group := 
mk_ob $ stabilizer (evaluation_action s_5_6_12) 
  (classical.choice $ nonempty_steiner_system dec_trivial)

/--The group $M_{12}$ is the automorphism group of the steiner system $S(5,6,12)$.-/
def M12 : Group := mk_ob $ Aut(s_5_6_12)

/-- The group $M_{22}$ is the stabilizer of two arbitrary points of the steiner system $S(5,8,24)$
  under the evaluation action of its automorphism group. -/
def M22 : Group := 
have H : ∃x : s_5_8_24 × s_5_8_24, x.1 ≠ x.2, from omitted,
mk_ob $ two_pt_stabilizer (evaluation_action s_5_8_24) (classical.some_spec H)

/-- The group $M_{23}$ is the stabilizer of an arbitrary point of the steiner system $S(5,8,24)$
  under the evaluation action of its automorphism group.-/
def M23 : Group := 
mk_ob $ stabilizer (evaluation_action s_5_8_24) 
  (classical.choice $ nonempty_steiner_system dec_trivial)

/-- The group $M_{24}$ is the automorphism group of the steiner system $S(5,8,24)$. -/
def M24 : Group := mk_ob $ Aut(s_5_8_24) 

/- the second happy family -/

/-- the Conway group Co₁ -/
def Co1 : Group := Co1
/-- the Conway group Co₂ -/
def Co2 : Group := Co2
/-- the Conway group Co₃ -/
def Co3 : Group := Co3
/-- the McLaughlin group -/
def McL : Group := McL
/-- the Higman–Sims group -/
def HS : Group := HS

section J2
private def a : free_group $ dfin 4 := ⟪(by to_dfin 0)⟫
private def b : free_group $ dfin 4 := ⟪(by to_dfin 1)⟫
private def u : free_group $ dfin 4 := ⟪(by to_dfin 2)⟫
private def v : free_group $ dfin 4 := ⟪(by to_dfin 3)⟫

/-- the Hall-Janko group J₂ -/
/- From the corresponding entry in the atlas of finite groups -/
def J2 : Group := ⟪dfin 4 | {a * b * u ⁻¹, a * b⁻¹ * v ⁻¹, a^2, b^3, u^15, (u^4 * v^2 * u^3 * v^3)^2, (u^3 * v * (u^2 * v^2)^2)^2} ⟫
end J2

/-- the Suzuki sporadic group -/
def Suz : Group := Suz

/- THE THIRD HAPPY FAMILY -/

-- todo: move monster here

/-- The baby monster group B is defined as follows:
if x be any element in conjugacy class 2A, 
then the centralizer C_M(x) is 2 ⬝ B, so B ≅ C_M(x)/Z(C_M(x)) -/
def BabyMonster : Group :=
let C := conj_class Monster 2 'A' in
let x := classical.some C.1.2 in
let Cx : set Monster := centralizer {x} in
mk_ob $ quotient_group.quotient $ is_subgroup.center $ Cx

/-- Fi24 is characterized by 3 ⬝ Fi24 ≅ N_M(x) where x is any element in conjugacy class 3A. 
  The derived subgroup of this group is the sporadic group Fi24' -/
/- todo: double check that quotienting out the span of x indeed gives Fi24. -/
def Fi24 : Group := 
let C := conj_class Monster 3 'A' in
let x := classical.some C.1.2 in
let N_Mx : set Monster := normalizer $ group.closure {x} in
let span_x : set N_Mx := induced_subgroup (group.closure {x}) N_Mx in
by exact mk_ob (quotient_group.quotient span_x)

/-- The Fischer group Fi24' -/
def Fi24' : Group := 
mk_ob $ derived_subgroup Fi24

/- A 3-transposition group is a “finite group G generated by a conjugacy class D of involutions, such that any two elements of D have a product of order at most 3, and … such that G’ = G” and any normal 2- or 3-subgroup of G is central. The elements of D are known as 3-transpositions, or just transpositions if there is no risk of confusion”  -/

def Y432 : Group := coxeter_group $ matrix_of_graph (coxeter_edges [4,3,2])

private def a : Y432 := generated_of $ torso _
private def b₁ : Y432 := generated_of $ arm (by to_dfin 0) (by to_dfin 0)
private def c₁ : Y432 := generated_of $ arm (by to_dfin 0) (by to_dfin 1)
private def b₂ : Y432 := generated_of $ arm (by to_dfin 1) (by to_dfin 0)
private def c₂ : Y432 := generated_of $ arm (by to_dfin 1) (by to_dfin 1)
private def b₃ : Y432 := generated_of $ arm (by to_dfin 2) (by to_dfin 0)
private def c₃ : Y432 := generated_of $ arm (by to_dfin 2) (by to_dfin 1)

/- We define Fi23 following p 232 of the atlas -/
/-- the Fischer group Fi23 -/
def Fi23 : Group :=
  category_theory.mk_ob $ quotient_group.quotient $
    is_subgroup.center $ (Y432)/⟪{(a*b₁*c₁*a*b₂*c₂*a*b₃*c₃)^10}⟫

/- We define Fi22 following p 162 of the atlas -/
/-- the Fischer group Fi22 -/
def Y332 : Group := coxeter_group $ matrix_of_graph (coxeter_edges [3,3,2])

private def a : Y332 := generated_of $ arm (by to_dfin 1) (by to_dfin 2)
private def b : Y332 := generated_of $ arm (by to_dfin 1) (by to_dfin 1)
private def c : Y332 := generated_of $ arm (by to_dfin 1) (by to_dfin 0)
private def d : Y332 := generated_of $ torso _
private def e : Y332 := generated_of $ arm (by to_dfin 0) (by to_dfin 0)
private def f : Y332 := generated_of $ arm (by to_dfin 0) (by to_dfin 1)
private def g : Y332 := generated_of $ arm (by to_dfin 0) (by to_dfin 2)
private def h : Y332 := generated_of $ arm (by to_dfin 2) (by to_dfin 0)
private def i : Y332 := generated_of $ arm (by to_dfin 2) (by to_dfin 1)

def Fi22 : Group := Y332/⟪{(a*b*c*d*e*f*h)^9, (b*c*d*e*f*g*h)^9, (b*c*d*e*f*d*h*i*d)^10}⟫

/-- the Thompson Group is C_M(x)/<x> for some element x in 3C -/
def Th : Group :=
let C := conj_class Monster 3 'C' in
let x := classical.some C.1.2 in
let C_Mx : set Monster := centralizer {x} in
let span_x : set C_Mx := induced_subgroup (group.closure {x}) C_Mx in
by exact mk_ob (quotient_group.quotient span_x)

/-- the Harada–Norton group	is C_M(x)/<x> for some element x in 5A -/
def HN : Group :=
let C := conj_class Monster 5 'A' in
let x := classical.some C.1.2 in
let C_Mx : set Monster := centralizer {x} in
let span_x : set C_Mx := induced_subgroup (group.closure {x}) C_Mx in
by exact mk_ob (quotient_group.quotient span_x)

/-- the Held group is C_M(x)/<x> for some element x in 7A -/
def He : Group := 
let C := conj_class Monster 7 'A' in
let x := classical.some C.1.2 in
let C_Mx : set Monster := centralizer {x} in
let span_x : set C_Mx := induced_subgroup (group.closure {x}) C_Mx in
by exact mk_ob (quotient_group.quotient span_x)

/- the pariahs  -/

/-- the Janko group J₁ -/
theorem J1_char : ∃!(G : Group.{0}), ∃(h : fintype G), 
by { exactI
  simple_group G ∧ 
  (∃(s : set G), is_Sylow_subgroup 2 s ∧ commutative_on s) ∧
  (∃x : G, x*x = 1 ∧ mk_ob (centralizer {x} : set G) ≅ 
    mk_ob (cyclic_group 2 × alternating_group 5)) } :=
omitted

def J1 : Group := classical.some J1_char

private def a := ⟪ff⟫
private def b := ⟪tt⟫

/-- the Janko group J₃ -/
/- From http://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J3G1-P1:
  
  Presentation 	〈 a, b | a2 = b3 = (ab)19 = [a, b]9 = ((ab)6(ab−1)5)2 = ((ababab−1)2abab−1ab−1abab−1)2 = abab(abab−1)3abab(abab−1)4ab−1(abab−1)3 = (ababababab−1abab−1)4 = 1 〉 -/
def J3 : Group := ⟪bool | {a^2, b^3, (a*b)^19, ⟦a, b⟧^9, ((a*b)^6*(a*b⁻¹)^5)^2, ((a*b*a*b*a*(b⁻¹))^2*a*b*a*b⁻¹*a*b⁻¹*a*b*a*b⁻¹)^2, a*b*a*b*(a*b*a*b⁻¹)^3*a*b*a*b*(a*b*a*b⁻¹)^4*a*b⁻¹*(a*b*a*b⁻¹)^3, (a*b*a*b*a*b*a*b*a*b⁻¹*a*b*a*b⁻¹)^4}⟫

/-- the Lyons group -/
def Ly : Group := sorry

/-- the O'Nan group -/

def O'N : Group := sorry

/-- the Janko group J₄ -/

private def x : free_group $ dfin 3 := ⟪(by to_dfin 0)⟫
private def y : free_group $ dfin 3 := ⟪(by to_dfin 1)⟫
private def t : free_group $ dfin 3 := ⟪(by to_dfin 2)⟫

/--
Atlas entry for J4 presented on its G2-`standard' generators.

G<x,y,t>:=Group<x,y,t|
x^2,
y^3,
(x*y)^23,
(x,y)^12,
(x,y*x*y)^5,
(x*y*x*y*x*y^-1)^3*(x*y*x*y^-1*x*y^-1)^3,
(x*y*(x*y*x*y^-1)^3)^4,
t^2,
(t,x),
(t,y*x*y*(x*y^-1)^2*(x*y)^3),
(y*t^(y*x*y^-1*x*y*x*y^-1*x))^3,
((y*x*y*x*y*x*y)^3*t*t^((x*y)^3*y*(x*y)^6*y))^2
>;
-/

def J4 : Group := ⟪ dfin 3 | {
  x^2,
  y^3,
  (x*y)^23,
  ⟦ x, y ⟧^12,
  ⟦ x, y*x*y ⟧^5,
  (x*y*x*y*x*y⁻¹)^3*(x*y*x*y⁻¹*x*y⁻¹)^3,
  (x*y*(x*y*x*y⁻¹)^3)^4,
  t^2,
  ⟦t,x⟧,
  ⟦t,y*x*y*(x*y⁻¹)^2*(x*y)^3⟧,
  (y*(t ↑↑ y*x*y⁻¹*x*y*x*y⁻¹*x))^3,
  ((y*x*y*x*y*x*y)^3 * t * (t ↑↑ (x*y)^3*y*(x*y)^6*y))^2
} ⟫ 

/-- the Rudvalis group -/
def Ru : Group := sorry
