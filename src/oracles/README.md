## Oracles

We can understand the concept of an __Oracle__ as an entity or middleware which is responsible of querying the data from a big set of elements given some precise coordinates and returns us the exact value associated to the coordinates we gave.

This concept is taken and slightly modified from [`Halo2`](https://github.com/zcash/halo2).

Oracles have not only the ability of store and retrieve circuit-related information such as it's description or witness values, but also, they provide a way to generate polynomials with this information, as well as ways to evaluate these at a particular point or also, store the evaluations that have been requested to do.

One can see the Oracles as a backend for an specific type of data of the circuit which is able not only to store it, but also to track all the queries made to it. Once the Prover wants to start proving, it can ask the oracle for all the polynomial information needed in respect to this particular circuit data.

We have 3 main types of oracles:
### Fixed Oracles
Fixed Oracles define polynomials whose coefficients are part of the circuit-definition. This represents mainly selector wires (which don't have it's own oracle as opposite to Halo2) and also constant values that are tied to the circuit definition rather than witness.

These can be digested at `preprocessing` time and do not vary in-between proof generations.

### Instance Oracles
Instance oracles define the Public Inputs passed on each proof generation. They inherit the name from `Halo2 Instance Column`s and they have the exact same underlying mechanism. All of the Oracle-stored data needs to be re-computed in-between proofs.


### Witness Oracles
Witness Oracles define polynomials whose coefficients are part of the circuit-witness data. These are the same as `Advice Column`s in `Halo2`.
These values might change on each proof generation and, all of the Oracle-stored data needs to be re-computed in-between proofs.