# Add new SMT solver types as .props files

This is an examplary solver properties file. 
To add a solver, specify a *.props* file following this example or the existing files and add it to the *key.core\src\main\resources\de\uka\ilkd\key\smt\st* directory. 
For the solver to be usable, add the file's name to *defaultSolvers.txt*.

## Specifiable properties

The solver's name. 
Should be unique amongst all used solver properties files, otherwise it is renamed throughout the solver loading process.
If no name is given, the solver will be called "SMT Solver" or a unique version of that (depending on the other solvers' names).
```properties
name=Z3
```

Arbitrary information about the specified solver.
```properties
info=Some text.
```

The cmd command used to start the solver process. Empty String by default, if the property is not specified.
Can later be changed by the user in the settings.
The current command can later be changed by the user in the settings.
```properties
command=startSolver
```

The cmd parameters appended to the command when starting the solver program, e.g. "-in" and "-smt2".
If the property is not specified, the params are an empty String by default. They can later be changed by the user in the settings.
```properties
params=--params
```

The version parameter appended to the command while starting the solver program in order to get its version.
If the property is not specified, it is an empty String "". Note that this cannot be changed later by the user.
```properties
version=--version
```

The minimum supported version of this solver. By default, this is an empty String. 
Note that different versions are compared to this minimum version lexicographically - if that comparison is not possible, you may have to override the SolverTypeImplementation class.
```properties
minVersion=0.0.0
```

The delimiters used by the solver program in its stdout messages. Default value is the array {"\n", "\r"}.
```properties
delimiters=delimiter1, delimiter2\
  delimiter3, delimiter4,\
  delimiter5
```

The default solver process timeout (in seconds) as a long value. 
If the property is not set or <= -1, it is -1 by default, meaning that the general SMT timeout is used.
The current timeout can later be changed by the user in the settings.
```properties
timeout=60
```

The fully specified class name of the SMTTranslator class used by the solver at hand.
Currently possible values for TRANSLATOR_CLASS:
SmtLib2Translator (legacy solvers), ModularSMTLib2Translator
```properties
translatorClass=de.uka.ilkd.key.smt.TRANSLATOR_CLASS
```

The SMTHandlers used by this solver. 
If the property is not specified, it is an empty list by default which leads to all handlers being used.
Note that this property currently only takes effect if the ModularSMTLib2Translator class is used.
The handlers' names are expected to be fully specified. Currently possible values of HANDLER_CLASS are for example: 
BooleanConnectiveHandler, CastHandler, CastingFunctionsHandler, DefinedSymbolsHandler, FieldConstantHandler, InstanceOfHandler, ...
```properties
handlers=de.uka.ilkd.key.smt.newsmt2.HANDLER_CLASS,\
	...
```

The handler options (a list of arbitrary Strings) for the SMTHandlers used by the SMTTranslator. 
If the property is not specified, it is an empty list by default leading to default behavior of the SMTHandlers.
All the used handlers handle the options on their own.
```properties
handlerOptions=option1,\
	...
```

The message handler (see SolverSocket.MessageHandler) used by the solver socket for communication with this solver.
Currently possible values: DEFAULT (as is used by Z3), CVC4, CVC5, Z3CE
```properties
messageHandler=msg_handler_name
```
 		
The preamble file's name (has to be in this same resource directory). 
By default, the preamble.smt2 file is used.
```properties
preamble = specialPreamble.smt2
```

If this is true, the solver is only usable in experimental mode. Generally, those are the solvers that still use the SmtLib2Translator instead of the ModularSMTLib2Translator. The property is false by default, if not specified.
```properties
legacy=true/false
```
