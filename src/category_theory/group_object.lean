-- Copyright (c) 2019 Jesse Han. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jesse Han

import .finite_limits

open category_theory category_theory.limits category_theory.limits.finite_limits
     category_theory.limits.binary_product

universes u v

variables (C : Type u) [𝒞 : category.{v u} C]
include 𝒞 

local infix ` × `:60 := binary_product

local infix ` ×.map `:60 := binary_product.map

structure group_object [has_finite_products C] : Type (max u v) :=
-- (G : C)
-- (mul : (G × G) ⟶ G)
-- (mul_assoc : (reassoc_hom G) ≫ (@binary_product.map C _ (by apply_instance) _ _ _ _ 𝟙 _ mul) ≫ mul = (mul ×.map (𝟙 _)) ≫ mul)
-- (one : term ⟶ G)
-- (one_mul : (𝟙 G) = one_mul_inv _ ≫ (one ×.map (𝟙 G)) ≫ mul)
-- (mul_one : (𝟙 G) = mul_one_inv _ ≫ ((𝟙 G) ×.map one) ≫ mul)
-- (inv : G ⟶ G)
-- (mul_left_inv : (𝟙 G) = (map_to_product.mk (inv) (𝟙 G)) ≫ mul ) 
