example.name = Lambda Expressions
example.path = Java 25
example.file = project.key
example.additionalFile.1 = Lambdas.java

Lambda expressions are supported in KeY by a transformation into
anonymous local classes implementing the functional interface (following
the approach of Alexander Csiky's bachelor thesis).

The JML specification of a lambda expression is given as comments in its
body and converted into model methods on the generated class:
`requires` into `preCondition(...)`, `ensures` into
`postCondition(...)` (a `two_state` model method whose parameter
`__result` holds the return value of the functional method) and
`assignable` into `frameCondition(...)`. The functional interface
declares these model methods and specifies its abstract method against
them (here: `requires preCondition(x)`, `ensures postCondition(x,
\result)`, `assignable frameCondition(x)`).

The proof obligation proves the generated implementation of the
functional method (`Lambdas.IntFunction__1::apply` in `project.key`),
i.e. that the lambda body satisfies the contract derived from its
clauses. It is verifiable without user interaction.
