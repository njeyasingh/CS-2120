

--Math

---mnl6sc@virginia.edu https://github.com/mlarusso/CS-2120.git
---npj5kr@virginia.edu https://github.com/njeyasingh/CS-2120.git
--fpg2kv@virginia.edu https://github.com/franklin-glance/cs2120f21.git

/-


Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.

Nikita Jeyasingh
Mia Larusso
Franklin Glance 
-/

-- 1
example : true := true.intro

--2

example : false :=   -- trick question? why?
-- when something is deemed false, it cannot be proven true. it is already false, thus - it being a trick question

-- idk why this is an error at "example" it should be right since it came directly from the homework 

-- 3 
example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro,
  -- forward 
  assume porp,
  apply or.elim porp,
  assume p,exact p,
  assume p,exact p,
  --backwards
  assume p,
  exact or.intro_left P p,
end

-- 4 
example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
assume p,
apply iff.intro ,
assume pP,
apply and.elim_right pP,
assume p,
exact and.intro p p,
end


-- 5 
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro,
  assume PQ,
  apply or.elim PQ,
  assume p, 
  apply or.intro_right,exact p,
  assume Q,
  apply or.intro_left, exact Q,
 
 -- GO THE OTHER WAY AROUND -- IDENTITY PROOF BASICALLY
    assume QP,
    apply or.elim QP,
    -- not working for some reason
    assume P,
    -- I don't understand why this isn't working. I've changed it so many times I do not understand so I'm leaving it like this. 
    apply or.intro_left, exact P,
    assume Q,
    apply or.intro_right, exact Q,    
end


--6 
example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro ,
  --forward
  assume PQ,
 -- idk why this isn't working either
 -- so I am giving up on this problem
  apply and.intro(and.elim_right PQ) 
  and.elim_left PQ,
  --backward
  assume QP,
  apply and.intro(and.elim_right QP) 
  and.elim_left QP,
end


--7 
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume prop,
  have qr:
  Q ∨ R:= and.elim_right prop,
  have p:
  P:= and.elim_left prop,
  -- apply it to each invididually
  apply or.elim qr,
  assume Q,
  apply or.intro_left,
  apply and.intro p Q,
  assume R,
  apply or.intro_right,
  apply and.intro p R,
--backward
  assume right,
  apply or.elim right,
  assume pq,
-- assume left side 
  apply and.intro,
  apply and.elim_left pq,
  apply or.intro_left, apply and.elim_right pq,
  assume pr,
  -- for both the left and right
  apply and.intro,
  apply and.elim_left pr,
  apply or.intro_right, apply and.elim_right pr,  
end


-- 8
example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
    assume P Q R,
  apply iff.intro,
  --forwards
  assume left,
  apply or.elim left,
  -- left
   assume p,
    apply and.intro _ _, 
     apply or.intro_left, apply p,
    apply or.intro_left, apply p
    --right side of or
      assume qr,
      have q:Q:= and.elim_left pqro,
      have r:R:= and.elim_right qr,
      apply and.intro _ _,
        apply or.intro_right, 
        exact q,
        apply or.intro_right,
        exact r,
  --backwards
  assume right,
  have porq: P∨Q:= and.elim_left right,
  have pqr: P ∨ R:= and.elim_right right,
  cases pqro,
  apply or.intro_left,
  exact porr,
  apply or.intro_right, apply and.intro porq pqro,
end


-- 9
example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q, 
  apply iff.intro,
  assume left,
  apply and.elim_left left,
  --backwards
  assume p,
  apply and.intro,
  exact p,
  apply or.intro_left, 
  exact p,
end


-- 10
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
   assume P Q,
  apply iff.intro,
  assume left,
  apply or.elim left,
  assume p,exact p,
  assume pq,
  apply and.elim_left pq,
  --backwards
  assume p,
  apply or.intro_left,
  apply p,
end


-- 11
example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
assume P,
apply iff.intro,
assume portrue,
apply or.elim portrue,
assume p, apply true.intro,
-- making assumption that tru: true
assume tru, exact true.intro,
assume tru, 
apply or.intro_right,
apply tru,

end

--12
example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
assume P,
-- comparing for the right side i think
apply iff.intro,
assume right,
cases right,
apply right,
cases right,
assume p,
-- comparison from the left to have both
apply or.intro_left, exact p,
end


--13
example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
assume P,
apply iff.intro,
assume P,
apply and.elim_left P,
assume p,
apply and.intro p true.intro,
end


-- 14
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
-- assume left case
assume P,
apply iff.intro,
assume left,
cases left,
exact left_right,
-- assume that something's false
assume NJ,
exact false.elim NJ,
end
