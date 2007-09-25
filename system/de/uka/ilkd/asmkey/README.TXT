This document describes briefly the major changes for the ASM KeY
version.

Author: Hubert Schmid
Date:   June, 2003


There are five major parts:


(1) Additional classes for ASM terms, formulas and taclets.

    The classes in the package 'de.uka.ilkd.asmkey.logic' extend
    classes from the core system (de.uka.ilkd.key.logic), that
    represent ASM modal operators and ASM rules (programs). There are
    also some additional meta operators, for applying transformations
    within taclets, that are not possible with pure taclet syntax.

    The package 'de.uka.ilkd.asmkey.rule' contains additional
    (variable) conditions, that restrict the application of taclets
    (e.g. rigid terms, ...). There is also the definition of the
    builtin step rule.


(2) Reading and parsing ASM terms, formulas and taclets.

    The package 'de.uka.ilkd.asmkey.parser.ast' contains all classes
    representing the abstract syntax tree of the input. The package
    'de.uka.ilkd.asmkey.parser.antlr' contains the parser
    specification, that builds an abstract syntax tree from an input
    stream (or string). In contrast to the core parser specifications
    (de.uka.ilkd.key.parser), this parser uses a strict separation
    between syntactical analysis (parsing context grammer) and
    analysis of static semantics (binding variables, sorts, types,
    etc.) The parser builds an intermediate representation (abstract
    syntax tree), that doesn't depend on anything else.

    The packages 'de.uka.ilkd.asmkey.env' and
    'de.uka.ilkd.asmkey.tree' perform analysis on the abstract syntax
    tree (variable binding, etc.) and create concrete terms and
    taclets.

    The input parser in the core system is selected dynamically with
    the Service class (see de.uka.ilkd.key.util.Service for more
    information). To use the ASM KeY parser, there should be a file
    'META-INF/services/de.uka.ilkd.key.parser.SimpleTermParser' in the
    classpath, that contains the name of the TermParser class,
    i.e. 'de.uka.ilkd.asmkey.parser.tree.AsmStringTermParser'.


(3) Printing ASM terms and formulas with Sequent Printer.

    The package 'de.uka.ilkd.asmkey.pp' contains additional classes
    for printing ASM terms and formulas on a SequentPrinter. The
    NotationInfo in the core system is selected dynamically with the
    Service class (see de.uka.ilkd.key.util.Service fore more
    information). To use the ASM KeY notation info, there should be a
    file 'META-INF/services/de.uka.ilkd.key.gui.NotationInfo' in the
    classpath, that contains the name of the ASM Key NotationInfo
    class, i.e. 'de.uka.ilkd.asmkey.pp.AsmNotationInfo'.


(4) Initializing and starting the standalone prover.

    The initializiation of the core system does a lot of things, that
    are not nessary for the ASM KeY standalong prover (e.g. different
    arithmetic types). Also the ASM KeY system uses a different method
    for loading the default taclets.

    Therefore almost the complete initializiation ist done by the
    class 'de.uka.ilkd.asmkey.gui.Main'. This class extends the Main
    class of the core system to reuse most common parts.


(5) Loading previously saved proofs.

    The loading (and saving) of proofs in the core system is currently
    work in progress. The current proof loading is tied tightly with
    the parser of the core system, and uses an "event driven" method
    for reconstructing proofs. Because the ASM KeY system uses a
    different parser, that works indenpently of concrete syntax, the
    proof loading can not be done directly from the parser
    specification.

    Therefore the proof loading is reimplemented for the ASM KeY
    system in the package 'de.uka.ilkd.asmkey.proof' and in the class
    'de.uka.ilkd.asmkey.gui.ProofLoader'.


There is further documentation in the files:

    logic/package.html
    parser/ast/package.html
    parser/antlr/README.TXT
    parser/package.html
    pp/package.html
    proof/package.html
    rule/package.html
