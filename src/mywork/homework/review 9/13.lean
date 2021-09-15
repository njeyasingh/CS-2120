/-
How do I write a conditional: 
- axioms( P Q : Prop) - arbitrary propositions shorthands for expressive identifiers 

Elimination rule: 


Rules for and and US implies


4. halve in le


-/

axioms (P Q : Prop)

def if_P_is_true_so_is_Q: Prop := P 

axiom p : P 
-- assume P is true
-- assume we have a proof of P (p) 

axiom pq: P  -> Q 
-- assume that we have a proof, pq, of P 

-- intro for imples: assumke premise, show conclusion 
-- e;o,omatopm rule for implies: 
#check pq

/- suppose that P and Q are propositionas and you know that pp   and that P are both true. 

show that W is tture. 

Proof: apply the truth of pq to the truth of P to derive teh truth of Q. 

Proof: By the elimination tule for -/

-- Doesn't t have property P? 

end all 

