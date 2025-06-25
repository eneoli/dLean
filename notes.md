just wanted to mention a "trick" regarding induction hypotheses.
For the coincidence lemma, if we forget the interpretation, it looks roughly like so 

`∀v w, H v w → ∀ t, P t v w`

In the current induction, we fix the states v, w, and the proof `H v w`. So for the case of addition (t = t1 + t2), we will have a goal like so:

v
w
H v w
P t1 v w
P t2 v w 
------------------- 
P (t1 + t2) v w

But, we do not need to fix everything before the induction. In fact, the first formula is equivalent to

`∀ t, ∀v w, H v w → P t v w`

This actually makes your induction stronger. Now the case for addition will now be:

∀v w, H v w → P t1 v w
∀v w, H v w → P t2 v w
----------------------------------------
∀v w, H v w → P (t1 + t2) v w

It might not be clear immediately that this is stronger, but if you just do an `intros`, you have:

v
w
H v w
∀v w, H v w → P t1 v w
∀v w, H v w → P t2 v w
--------------------------------
P (t1 + t2) v w

Same conclusion, but stronger hypotheses. In general, this adds more tactics because we need more `intros` and stuffs, but it is sometimes mandatory. One easy way to use this trick is using the tactic `revert` to move back hypotheses in the goal before using the induction scheme. I talk about this because of the differential case. I saw 

have moop : ∀y, denote i (v' y) t = denote i (w' y) t := by


This definitely looks like it should use the above trick. Using my notation from prior, this would be `P t v' w'`, so it could be proved by using the induction hypothesis providing a proof of `H v' w'`. I hope it's clear enough.

Have a good weekend, Enguerrand 
