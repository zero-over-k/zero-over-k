# Virtual Oracles

As we want to express more complex things, we need to combine basic `Oracle`s such as `WitnessOracle` or `FixedOracle` in order to elaborate more complex expressions that we need in our gates.
Well, this is where __Virtual Oracles__ come to save the day.

A VirtualOracle is an abstraction which contains the logic for a "circuit gate". To explain a bit further, this means that a VirtualOracle contains among other information, all of the constraints that define what we would understand as a __Custom Gate__ in plonk terms. This means that it doesn't only contain the polynomial equation that needs to hold (ie. be equal to 0). But also contains references to all of the basic oracles involved on the gate and a list of all of the queries that need to be performed to the other oracles from this one so that all of the constraints could be filled in with data.

VirtualOracles still hold all the same functionallity than primitive ones. But allow to indeed create more complex constraints or gates. They can also be composed with eachother on an infinite number of layers. So that at the end, **you're performing batches of 0 over K VirtualOracles*.

To understand what Virtual Oracles are, we first need to understand `VirtualQuery`es and `VirtualExpression`s.

## VirtualQuery
As you can see [with Oracles](Place the link where this lands in GH), we have 3 different types which can be queried to return