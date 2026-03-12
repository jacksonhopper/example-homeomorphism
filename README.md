# example-homeomorphism

I am learning to use Lean4 and mathlib to verify proofs I learned studying math, and hopefully explore proofs that are new to me.

This first example is from topology. It demonstrates the open unit interval, called (Ioo 0 1) in mathlib syntax, is homeomorphic to the real line \R. In Lean, Homeomorphism is a structure that requires the definition of two functions as well as proofs that the two functions are continuous and inverse. The declaration of such an object can then be used in a one-line proof of the statement the two spaces are homeomorphic, as demonstrated below the definition of the homeomorphism.

Because I am just learning, this proof is inelegant and dives into many more details than a fluent Lean programmer would typically get bogged down with. In the near future I plan to edit it into a more readable and compact proof that can be inspected by a human.
