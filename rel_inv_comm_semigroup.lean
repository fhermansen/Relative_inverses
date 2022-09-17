/-
Copyright (c) 2022 Flemming Hermansen. 
Released under Apache 2.0 license as described in 
https://www.apache.org/licenses/LICENSE-2.0
Authors: Flemming Hermansen
-/

import tactic
import tactic.basic
import field_theory.separable

/-
This file defines the property 'is_rel_inv a b' for elements in a semigroup. 
This property means that a is the inverse relatively to a unique idempotent element (a*b). 
The definition does not mention a zero element, so it does not need a semiring structure.
Zero has zero as its relative inverse. 
Non-zero nilpotent elements can not have a relative inverse.
Properties of the relative inverse if it exists:
The relation is commutative. A relative inverse element is unique if it exists.
Being relative inverses transfers along any possibly non-unital homomorphism.
All elements in a field have relativerse elements. 
Products of semigroups preserve the property that all the elements have relative inverses.

Later it will be shown that 
all algebraic separable elements in a commutative algebra over a field have
relative inverses.

Relative inverses can be used to prove that certain principal ideals are 
isomorphic to fields. 

Another application is to prove that certain ideals are maximal by producing a one-element
if the ideals are extended.
-/

section inv_a

open_locale classical
open_locale big_operators
noncomputable theory

def is_rel_inv {A : Type} [comm_semigroup A] (a b : A) :=
-- let e := (a * b) in 
(a * b) * (a * b) = (a * b) ∧ -- (a * b) is idempotent and b = inv a is the relative inverse 
(a * b) * a = a ∧ -- the idempotent acts as a one-element for a
(a * b) * b = b. -- the idempotent acts as a one-element for b
-- if a = 0 then b = inv a = 0 and (a * b) = 0, but 0 is not mentioned explicitly

def all_rel_inv (A : Type*) [comm_semigroup A] : Prop := 
∀ (a : A), ∃ (b : A), is_rel_inv a b

lemma rel_inv_comm {A : Type} [comm_semigroup A] {a b : A} : is_rel_inv a b → is_rel_inv b a :=
begin
  unfold is_rel_inv, 
  intros h, cases h with he h, cases h with ha hb,
  simp only [mul_comm b _],
  split, assumption,  split, assumption, assumption,
end

lemma rel_inv_is_unique {A : Type} [comm_semigroup A] (a b b' : A)
: is_rel_inv a b ∧ is_rel_inv a b' → b = b' :=
begin
  intros h, cases h with hb hb', 
  unfold is_rel_inv at hb, unfold is_rel_inv at hb',
  rcases hb with ⟨he, hea, heb⟩, rcases hb' with ⟨he', hea', heb'⟩,
  have e_eq : a * b = a * b',
  begin
    calc a * b = ((a * b') * a ) * b : by rw hea'
    ... = ((a * b) * a) * b' : by simp only [mul_comm, mul_assoc]
    ... = a * b' : by rw hea
  end,
  have b_eq_b' : b = b',
  begin
    calc b = (a * b) * b : by rw heb
    ... =(a * b') * b : by rw e_eq
    ... = (a * b) * b' : by simp only [mul_comm, mul_assoc]
    ... = (a * b') * b' : by rw e_eq
    ... = b' : by rw heb'
  end,
  assumption,
end

lemma inv_invariant_hom_a_b {A : Type} [comm_semigroup A] {A' : Type} [comm_semigroup A'] 
(h : A →ₙ* A') { a b : A} : is_rel_inv a b → is_rel_inv (h.to_fun a) (h.to_fun b) := 
begin
  -- →ₙ* means a non_unital_homomorphism
  intros hl1,
  rcases hl1 with ⟨he, ha, hb⟩,
  unfold is_rel_inv,
  have mul1 : ∀ (x y : A), h.to_fun (x * y) = h.to_fun x * h.to_fun y,
    by exact h.map_mul,
  -- h_map_mul': ∀ (x y : A), h_to_fun (x * y) = h_to_fun x * h_to_fun y
  repeat {rw ← (mul1 _ _)},
  rw he, rw ha, rw hb,
  split, refl, split, refl, refl,
end

lemma inv_invariant_a_b {A : Type} [comm_semigroup A] {A' : Type} [comm_semigroup A'] 
(h : A ≃* A') { b : A} {a' : A'}: 
(h.inv_fun a' * b) * (h.inv_fun a' * b) = (h.inv_fun a' * b) ∧ 
(h.inv_fun a' * b) * h.inv_fun a' = h.inv_fun a' ∧  
(h.inv_fun a' * b) * b = b → 
(a' * h.to_fun b) * (a' * h.to_fun b) = (a' * h.to_fun b) ∧ 
(a' * h.to_fun b) * a' = a' ∧  
(a' * h.to_fun b) * h.to_fun b = h.to_fun b := 
begin
  intros hl1,
  rcases hl1 with ⟨he, ha, hb⟩,
  have ha' : a' = h.to_fun (h.inv_fun a'), 
  begin 
    rw ← (h.right_inv a'), simp,
  end,
  rw ha', 
  have mul1 : ∀ (x y : A), h.to_fun (x * y) = h.to_fun x * h.to_fun y,
    by exact h.map_mul,
  -- h_map_mul': ∀ (x y : A), h_to_fun (x * y) = h_to_fun x * h_to_fun y
  repeat {rw ← (mul1 _ _)},
  rw he, rw ha, rw hb,
  split, refl, split, refl, refl,
end

lemma rel_inv_invariant_isomorphism' {A : Type} [comm_semigroup A] {A' : Type} [comm_semigroup A'] 
(h : A ≃* A') : all_rel_inv A → all_rel_inv A' := 
begin
  unfold all_rel_inv, unfold is_rel_inv, 
  intros hl, intros a', 
  specialize hl (h.inv_fun a'), cases hl with b hl1,
  use  h.to_fun b, 
  apply inv_invariant_a_b h, assumption,
end

lemma field_all_rel_inv {A : Type} [field A] : all_rel_inv A :=
begin
  unfold all_rel_inv, unfold is_rel_inv, 
  intros a, 
  by_cases ha0 : a=0,
  {rw ha0,simp}, -- a = 0
  -- now ha0 : a ≠ 0
  have ha_div_a : a * (1/a) = 1, by exact mul_div_cancel' 1 ha0,
  use 1/a, rw ha_div_a, ring_nf, simp,
end

-- Products preserve all_rel_inv
lemma product_all_rel_inv {A : Type*} [comm_semigroup A] {A' : Type*} [comm_semigroup A']  
  : ( all_rel_inv A) → ( all_rel_inv A')  → all_rel_inv (A × A') :=
  begin 
    unfold all_rel_inv is_rel_inv, 
    intros hA hA' c, 
    cases c with a a', specialize hA a, specialize hA' a',
    cases hA with b hA, cases hA with he hA, cases hA with ha hb,
    cases hA' with b' hA', cases hA' with he' hA', cases hA' with ha' hb',
    use ⟨ b, b' ⟩,
    split, simp, exact and.intro he he',
    split, simp, exact and.intro ha ha',
    simp, exact and.intro hb hb',
  end

  end inv_a
