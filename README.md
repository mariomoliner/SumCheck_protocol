# Sum-Check protocol

A rust implementation of the Sum check protocol as devised by Justin Thaler on Proofs, Arguments, and Zero-Knowledge.

The Sum check protocol is a fundamental tool in verifiable computing. It allows to prove interactively to a verifier the computation of the boolean hypercube on some multivariate polynomial over a finite field. This result translates into many settings in the mark of verifiable computation.

This is one of my first experiences with Rust so the code might be far from optimal.

## Non Interactive Sum-Check

As originally devised the Sum-Check protocol is an interactive one. There's a non-interactive version using the Fiat-Shamir transformation.

We calculate the different Basefield scalars in the following manner

$ c_i = SHA256(g_1,...,g_i)$

Note that the hash function SHA256 here acts as random oracle "substitute".
The verifier receives the list of g_i's and as he has access to the random oracle can run the verifications.

Using this scheme soundness is guaranteed in the same security level as in the non interactive version.