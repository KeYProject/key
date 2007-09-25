The parser uses a strict separation of context free grammar and
semantic analysis (like variable binding and types). The parser builds
an abstract syntax tree, that represents only the context free
grammer. The semantic analysis is done later by the package
"parser.tree".

There is no explicit documentation for the ASM KeY syntax. Please read
the ANTLR parser specification 'AsmKeyParser.g' for more information
about the syntax.

