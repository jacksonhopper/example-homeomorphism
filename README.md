# example-homeomorphism

This proof example is from topology. It demonstrates the open unit interval, called (Ioo 0 1) in mathlib syntax, is homeomorphic to the real line \R. In Lean, Homeomorphism is a structure that requires the definition of two functions as well as proofs that the two functions are continuous and inverse. The structure (Ioo 0 1) \sim\_t \R is not a proposition, so the construction is not proof-irrelevant. However the structure can then be used in a one-line proof of the proposition that the two spaces are homeomorphic, as demonstrated below the definition of the homeomorphism.

The proof is somewhat inelegant and dives into many more details than strictly necessary. I may edit it in the future into a more readable and compact proof that is easier for a human to inspect. 
