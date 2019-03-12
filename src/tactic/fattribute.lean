/-
Copyright (c) 2019 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

The fabstract user attribute.
-/

import tactic.metadata
import system.io

open interactive interactive.types lean.parser tactic native io

@[user_attribute]
meta def fabstract_attr : user_attribute (rb_map name (string)) (list name) :=
{
  name := `fabstract,
  descr := "The fabstract user attribute. Used to mark lemmas captured in order to capture meta data.",
  parser := many ident <|> pure [],
  cache_cfg := ⟨
    λ ns, ( do l ← mmap (trace_metadata_JSON) ns,
         pure $ rb_map.of_list (list.zip ns l))
   , [] ⟩
}

/- Tests -/
/-- Well, hello there! -/
-- @[fabstract ABC000 ABC200]
def test₁ : 1+1 =2 := by simp

-- @[fabstract ABC101 ABC200]
def test₂ : 1+1 =2 := by simp

/-- the Harada–Norton group is C_M(x)/<x> for some element x in 5A -/
@[fabstract ABC101 XYZ200]
def welp : 1+1 =2 := by simp

@[fabstract JBX190 AXX200]
def woolp : 1+1 =2 := by simp

@[fabstract]
def flump : 1+1 =2 := by simp

meta def query_cache (n : name) : tactic (string) :=
do m ← fabstract_attr.get_cache,
  v ← m.find n,
  pure v

meta def prod_list_to_JSON {key : Type} {data : Type} [has_to_format key][has_to_format data]: list (key × data) → string 
| [] :=  " "
| ((k,v) :: kvs) := if list.length kvs = 0 then to_string (format!"\"{k}\" :{v}}") else to_string (format!"\"{k}\" :{v},") ++ prod_list_to_JSON kvs

meta def rb_map_to_JSON {key : Type} {data : Type} [has_to_format key][has_to_format data] (m : rb_map key data) : tactic string :=
pure $ "{" ++ (prod_list_to_JSON $ rb_map.to_list m)


def write_json (cnts : string) : io unit := do
h ← mk_file_handle "fabstract.json" io.mode.write,
io.fs.write h cnts.to_char_buffer,
io.fs.close h

meta def mk_JSON_dump : tactic unit := 
do  m ← fabstract_attr.get_cache >>= rb_map_to_JSON,
    unsafe_run_io $ write_json m,
    skip

-- def read : state (ℕ × string) ℕ :=
-- do s ← get,
--    return s.1


-- def read_str : state (ℕ × string) string :=
-- do s ← get,
--    return s.2
-- -- def read_y : state (ℕ × ℕ × ℕ) ℕ :=
-- -- do s ← get,
-- --    return s.2.1


-- -- def read_z : state (ℕ × ℕ × ℕ) ℕ :=
-- -- do s ← get,
-- --    return s.2.2

-- def write (n : ℕ) : state ℕ unit :=
-- do s ← get,
--    put (n),
--    return ()

-- -- def write_y (n : ℕ) : state (ℕ × ℕ × ℕ) unit :=
-- -- do s ← get,
-- --    put (s.1, n, s.2.2),
-- --    return ()

-- -- def write_z (n : ℕ) : state (ℕ × ℕ × ℕ) unit :=
-- -- do s ← get,
-- --    put (s.1, s.2.1, n),
-- --    return ()

-- #check state_t string tactic

-- meta def test : state_t string tactic (ℕ)
-- := do s ← get,
--     put (s ++ "1"),
--     return (1)

-- -- #eval test.run ("hi")
-- #check fabstract_attr.get_cache 
-- run_cmd attribute.get_instances `fabstract >>= tactic.trace
-- run_cmd mk_JSON_dump
run_cmd do
  m ← fabstract_attr.get_cache,
  l ← rb_map_to_JSON m,
  tactic.trace l,
  skip 

