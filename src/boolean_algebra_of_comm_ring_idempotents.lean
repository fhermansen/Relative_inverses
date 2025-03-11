/-
Copyright (c) 2022 Flemming Hermansen. 
Released under Apache 2.0 license as described in 
https://www.apache.org/licenses/LICENSE-2.0
Authors: Flemming Hermansen
-/

import algebra.algebra.basic
import order.boolean_algebra

/-
This file prove that the idempotent elements in a commutative ring 
constitute a Boolean algebra.

idempotent_cri (A) [cr : comm_ring A] := { a : A // a * a = a}
subtype that contains all the idempotent elements from A.

instance boolean_algebra_comm_ring_idempotents [comm_ring A] : boolean_algebra (idempotent_cri A) 
The main result telling that elements of subtype 'idempotent_cri A'
can be used as elements in a Boolean algebra.

-/

section comm_ring_idempotents

variables  {A : Type*} [comm_ring A] 

variables {B : Type*} [boolean_algebra B] 

open_locale classical

noncomputable theory

def idempotent_cri (A) [cr : comm_ring A] := { a : A // a * a = a}

namespace idempotent_cri

instance coe_idempotent_cri : has_coe (idempotent_cri (A)) A := ⟨λ (e : idempotent_cri (A)), e.val⟩

instance inhabited_idempotent_cri : inhabited (idempotent_cri A) := ⟨⟨1, mul_one 1⟩⟩

def property' (e : idempotent_cri A) : (↑e : A) * ↑e = ↑e := by exact e.property.

def property'' (e : idempotent_cri A) : (e.val : A) * e.val = e.val := by exact e.property.

@[simp, reducible]
def prop_inf_cri [hr : comm_ring A] (a : idempotent_cri A) (b : idempotent_cri A) : 
((a.val : A) * b.val) * (a.val * b.val)  = (a.val * b.val) :=
begin
    simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
    simp only [mul_comm _ b.val,  ← mul_assoc, b.property''], -- idempotent b
    simp only [mul_comm _ a.val,  ← mul_assoc, a.property''], -- idempotent a
end

@[simp, reducible]
def inf_cri [hr : comm_ring A] (a : idempotent_cri A) (b : idempotent_cri A) : idempotent_cri A :=
begin
  exact ⟨ a * b, 
  begin
    simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
    simp only [mul_comm _ ↑b,  ← mul_assoc, b.property'], -- idempotent b
    simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- idempotent a
  end ⟩
end

@[simp, reducible]
def sup_cri [hr : comm_ring A] (a : idempotent_cri A) (b : idempotent_cri A) : 
idempotent_cri A :=
begin
  exact ⟨ ↑a + ↑b - ↑a * ↑b, 
  begin 
     simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
    simp only [mul_comm _ ↑b,  ← mul_assoc, b.property'], -- idempotent b
    simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- idempotent a
    ring,
  end ⟩,
end

@[simp, reducible]
def le_cri [hr : comm_ring A] (a : idempotent_cri A) (b : idempotent_cri A) := 
(↑a : A) * ↑b = ↑a

@[simp, reducible]
def lt_cri [hr : comm_ring A] (a : idempotent_cri A) (b : idempotent_cri A) :=
(↑a : A) * ↑b = ↑a ∧ (¬(↑a : A)= ↑b)

@[simp, reducible]
def top_cri [hr : comm_ring A] : idempotent_cri A := ⟨ 1, by ring ⟩

@[simp, reducible]
def bot_cri [hr : comm_ring A] : idempotent_cri A := ⟨ 0, by ring ⟩

@[simp, reducible]
def compl_cri [hr : comm_ring A] (a : idempotent_cri A) : idempotent_cri A := 
 ⟨ 1 - ↑a, 
by {simp only [sub_mul, mul_sub, mul_one, one_mul, a.property'], ring} ⟩

@[simp, reducible]
def sdiff_cri [hr : comm_ring A] (a b: idempotent_cri A) : idempotent_cri A := 
begin
  exact ⟨ ↑a - ↑a * ↑b, 
  begin
    simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
    simp only [mul_comm _ ↑b,  ← mul_assoc, b.property'], -- idempotent b
    simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- idempotent a
    ring,
  end ⟩,
end

@[simp]
instance has_le_comm_ring_idempotents [comm_ring A] : has_le (idempotent_cri A) :=
{ le := le_cri }

@[simp]
instance has_sup_comm_ring_idempotents [comm_ring A] : has_sup (idempotent_cri A) :=
{ sup := sup_cri }

@[simp]
instance has_inf_comm_ring_idempotents [comm_ring A] : has_inf (idempotent_cri A) :=
{ inf := inf_cri }

@[simp]
instance has_top_comm_ring_idempotents [comm_ring A] : has_top (idempotent_cri A) :=
{ top := top_cri }

@[simp]
instance has_bot_comm_ring_idempotents [comm_ring A] : has_bot (idempotent_cri A) :=
{ bot := bot_cri }

@[simp, reducible]
instance has_compl_comm_ring_idempotents [comm_ring A] : has_compl (idempotent_cri A) :=
{ compl := compl_cri }

@[simp]
instance has_sdiff_comm_ring_idempotents [comm_ring A] : has_sdiff (idempotent_cri A) :=
{ sdiff := sdiff_cri }

lemma sup_assoc_cri [comm_ring A] (a b c: idempotent_cri A) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
begin
  unfold has_sup.sup, simp, ring_nf, 
end

lemma sup_comm_cri [comm_ring A] (a b : idempotent_cri A) : a ⊔ b  = b ⊔ a :=
begin
  unfold has_sup.sup, apply subtype.eq, ring_nf, 
end

lemma inf_assoc_cri [comm_ring A] (a b c: idempotent_cri A) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
begin
  unfold has_inf.inf, apply subtype.eq, simp {proj := tt}, ring, 
end

lemma inf_comm_cri [comm_ring A] (a b : idempotent_cri A) : a ⊓ b  = b ⊓ a :=
begin
  unfold has_inf.inf, apply subtype.eq, ring_nf, 
end

set_option pp.coercions true.

lemma tt [comm_ring A] (a : idempotent_cri A) : ↑ a = a.val := by refl

lemma sup_inf_self_cri [comm_ring A] (a b : idempotent_cri A) : a ⊔ a ⊓ b = a :=
begin
  unfold has_inf.inf, unfold has_sup.sup,-- apply subtype.eq, --simp {proj := tt},
  rw inf_cri, rw sup_cri, apply subtype.eq, simp  {proj := true},
    simp  only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
      ← mul_assoc], -- flatten expression
    simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- idempotent a
    simp,
end

lemma inf_sup_self_cri [comm_ring A] (a b : idempotent_cri A) : a ⊓ (a ⊔ b) = a :=
begin
  unfold has_inf.inf, unfold has_sup.sup sup_cri, apply subtype.eq, simp {proj := true}, 
       simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
    simp only [mul_comm _ ↑b,  ← mul_assoc, b.property'], -- idempotent b
    simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- idempotent a
    simp,
end

@[simp]
def inf_sup_le_cri [comm_ring A] (a b c : idempotent_cri A) : 
  a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c :=
begin
  unfold has_sup.sup has_inf.inf has_le.le inf_cri sup_cri le_cri, 
  simp {proj := true}, 
  simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
  simp only [mul_comm _ ↑b,  ← mul_assoc, b.property'], -- idempotent b
  simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- idempotent a
  simp only [mul_comm _ ↑c,  ← mul_assoc, c.property'], -- idempotent c
  ring,
end

lemma le_sup_inf_cri [comm_ring A] (a b c : idempotent_cri A) : 
(a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ b ⊓ c :=
begin
  unfold has_sup.sup has_inf.inf has_le.le inf_cri sup_cri le_cri,  
  simp {proj := true}, 
  simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
  simp only [mul_comm _ ↑b,  ← mul_assoc, b.property'], -- idempotent b
  simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- idempotent a
  simp only [mul_comm _ ↑c,  ← mul_assoc, c.property'], -- idempotent c
  ring,
end

lemma le_sup_left_cri [comm_ring A] (a b : idempotent_cri A) : a ≤ a ⊔ b :=
begin
  unfold has_sup.sup has_le.le compl_cri sup_cri le_cri, 
  simp {proj := true}, 
  simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
  simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- sort, reflatten, a * a = a
  ring,
end

lemma sdiff_eq_cri [comm_ring A] (a b : idempotent_cri A) : 
a \ b = a ⊓ bᶜ :=
begin 
  apply subtype.eq, unfold has_inf.inf has_sdiff.sdiff has_compl.compl compl_cri, 
  simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
  simp only [mul_comm _ ↑b,  ← mul_assoc, b.property'], -- sort, reflatten, b * b = b
  simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- sort, reflatten, a * a = a
  ring_nf,
end

lemma top_le_sup_compl_cri [comm_ring A] (a : idempotent_cri A) : 
⊤ ≤ a ⊔ aᶜ :=
begin 
  unfold has_sup.sup has_compl.compl has_top.top has_le.le compl_cri sup_cri le_cri, 
  simp {proj := true}, 
  simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
  simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- sort, reflatten, a * a = a
  ring,
end

lemma inf_compl_le_bot_cri [comm_ring A] (a : idempotent_cri A) : 
a ⊓ aᶜ ≤ ⊥ :=
begin 
  unfold has_inf.inf has_compl.compl has_bot.bot has_le.le compl_cri sup_cri le_cri, 
  simp {proj := true}, 
  simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
  simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- sort, reflatten, a * a = a
  ring,
end

lemma le_antisym_cri [comm_ring A] (a b : idempotent_cri A) : a ≤ b → b ≤ a → a = b :=
begin 
  unfold has_le.le le_cri,
  intros hab hba,
  rw mul_comm at hab, rw hab at hba,
  apply subtype.eq, exact hba,
end

lemma sup_le_cri [comm_ring A] (a b c : idempotent_cri A) : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
begin
  unfold has_le.le has_sup.sup sup_cri le_cri, 
  intros hac hbc,
  simp {proj := true}, 
  simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
    mul_assoc], -- flatten expression
  rw hac, rw hbc,
end

lemma le_inf_cri [comm_ring A] (a b c : idempotent_cri A) : a ≤ b → a ≤ c → a ≤ b ⊓ c :=
begin
  unfold has_le.le has_inf.inf, simp only [inf_cri, le_cri],
  intros haba haca,
  simp {proj := true}, 
  simp only [ ← mul_assoc], -- flatten expression
  rw haba, rw haca,
end

lemma le_top_cri [comm_ring A] (a : idempotent_cri A) : a ≤ ⊤ :=
begin 
  unfold has_le.le has_top.top le_cri,
  simp {proj := true}, 
end

lemma bot_le_cri [comm_ring A] (a : idempotent_cri A) : ⊥ ≤ a :=
begin
  unfold has_le.le has_bot.bot le_cri,
  simp {proj := true}, 
end

lemma le_sup_right_cri [comm_ring A] (a b : idempotent_cri A) : b ≤ a ⊔ b :=
begin
  unfold has_le.le has_sup.sup le_cri sup_cri,
  simp {proj := true}, 
  simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
  simp only [mul_comm _ ↑b,  ← mul_assoc, b.property'], -- sort, reflatten, a * a = a
  ring,
end

lemma inf_inf_sdiff_cri [comm_ring A] (a b : idempotent_cri A) : a ⊓ b ⊓ a \ b = ⊥ :=
begin
  unfold has_inf.inf has_sdiff.sdiff inf_cri sdiff_cri,
  apply subtype.eq, simp {proj := true}, 
  simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
  simp only [mul_comm _ ↑b,  ← mul_assoc, b.property'], -- sort, reflatten, b * b = b
  simp only [mul_comm _ ↑a,  ← mul_assoc, b.property'], -- sort, reflatten, a * a = a
  ring_nf,
end

lemma inf_le_left_cri [comm_ring A] (a b : idempotent_cri A) : a ⊓ b ≤ a :=
begin
  unfold has_le.le has_inf.inf inf_cri le_cri,
  simp {proj := true}, 
  simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- sort, reflatten, a * a = a
end

lemma inf_le_right_cri [comm_ring A] (a b : idempotent_cri A) : a ⊓ b ≤ b :=
begin
  unfold has_le.le has_inf.inf inf_cri le_cri,
  simp {proj := true}, 
  simp only [mul_assoc, b.property'], -- flatten, b * b = b
end

lemma sup_inf_sdiff_cri [comm_ring A] (a b : idempotent_cri A) : a ⊓ b ⊔ a \ b = a :=
begin
  unfold has_inf.inf has_sup.sup has_sdiff.sdiff sup_cri inf_cri sdiff_cri,
  simp {proj := true}, 
  simp only [sub_mul, mul_sub, add_mul, mul_add, -- distributative
     ← mul_assoc], -- flatten expression
  simp only [mul_comm _ ↑a,  ← mul_assoc, a.property'], -- sort, reflatten, a * a = a
  simp only [mul_comm _ ↑b,  ← mul_assoc, b.property'], -- sort, reflatten, b * b = b
  simp {proj := true}, 
end

lemma le_reflexive_cri [comm_ring A] (a : idempotent_cri A) : a ≤ a :=
begin
  unfold has_le.le le_cri, rw a.property',
end

lemma le_trans_cri [comm_ring A] (a b c : idempotent_cri A) : a ≤ b → b ≤ c → a ≤ c :=
begin  unfold has_le.le le_cri, intros h1 h2, 
  rw ← h1, rw mul_assoc, rw h2,
end

lemma lt_iff_le_not_le_cri [comm_ring A] (a b : idempotent_cri A) : 
  ( a ≤ b ∧ (¬a.val = b.val)) ↔ a ≤ b ∧ ¬b ≤ a := 
  begin unfold has_lt.lt has_le.le le_cri, 
    split,
    -- ->
    intros h, cases h with hle hne,
    split, assumption,
    intros b_nle_a, 
    simp at hne {proj := true}, 
    rw ← hle at hne, rw mul_comm at hne,
    contradiction,
    -- <-
    intros h,
    cases h with aleb bnlea,
    split, assumption,
    rw mul_comm at aleb,
    simp {proj := true}, 
    rw ← aleb,
    intros h_contra,
    rw h_contra at bnlea,
    contradiction,
  end

@[priority 100]  -- see Note [lower instance priority]
instance boolean_algebra_comm_ring_idempotents [comm_ring A] : 
boolean_algebra (idempotent_cri A) :=
{ sup := sup_cri,
  le := le_cri,
  lt := lt_cri,
  le_refl :=le_reflexive_cri, 
  le_trans := le_trans_cri,
  lt_iff_le_not_le := lt_iff_le_not_le_cri,
  le_antisymm := le_antisym_cri,
  le_sup_left := le_sup_left_cri,
  le_sup_right := le_sup_right_cri,
  sup_le := sup_le_cri,
  inf := inf_cri,
  inf_le_left := inf_le_left_cri,
  inf_le_right := inf_le_right_cri,
  le_inf := le_inf_cri,
  le_sup_inf := le_sup_inf_cri,
  sdiff := sdiff_cri,
  bot := bot_cri,
  -- The following fields have been removed in the latest version of Mathlib
  -- sup_inf_sdiff := sup_inf_sdiff_cri,
  -- inf_inf_sdiff := inf_inf_sdiff_cri,
  compl := compl_cri,
  top := top_cri,
  inf_compl_le_bot := inf_compl_le_bot_cri,
  top_le_sup_compl := top_le_sup_compl_cri,
  le_top := le_top_cri,
  bot_le := bot_le_cri,
  sdiff_eq := sdiff_eq_cri }

@[reducible]
def simp_inf_cri [hr : comm_ring A] (a b : idempotent_cri A) : 
(a ⊓ b) = (⟨ a.val * b.val, prop_inf_cri a b ⟩ :  idempotent_cri A) :=
begin
  let ee := (⟨ a.val * b.val, prop_inf_cri a b ⟩ :  idempotent_cri A),
  have inf_eq : (a ⊓ b) = ee, by refl,
  exact inf_eq,
end

lemma bot_of_inf_sdiff_self {B : Type*} [boolean_algebra B] (e e': B)
: e ⊓ (e'\e) = ⊥ :=
begin
  rw sdiff_eq, 
  conv { to_lhs, congr, skip, rw inf_comm },
  rw ← inf_assoc, rw inf_compl_eq_bot, rw bot_inf_eq,
end

end idempotent_cri

end comm_ring_idempotents
