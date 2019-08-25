package de.uka.ilkd.key.nparser;

import antlr.RecognitionException;
import antlr.Token;
import antlr.TokenStream;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.visitor.DeclarationProgramVariableCollector;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.parser.*;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.IProofFileParser;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleKey;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.*;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.dl.translation.DLSpecFactory;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import org.antlr.v4.runtime.ParserRuleContext;
import org.key_project.util.collection.*;

import java.io.File;
import java.math.BigInteger;
import java.util.*;
import java.util.stream.Collectors;

import static de.uka.ilkd.key.proof.io.IProofFileParser.ProofElementID;

public class Builder extends KeYParserBaseVisitor<Object> {
    //region

    private static final Sort[] AN_ARRAY_OF_SORTS = new Sort[0];
    private static final Term[] AN_ARRAY_OF_TERMS = new Term[0];

    private static final int NORMAL_NONRIGID = 0;
    private static final int LOCATION_MODIFIER = 1;

    private static final String LIMIT_SUFFIX = "$lmtd";

    static HashMap<String, IProofFileParser.ProofElementID> prooflabel2tag = new LinkedHashMap<>(15);

    static {
        prooflabel2tag.put("branch", ProofElementID.BRANCH);
        prooflabel2tag.put("rule", ProofElementID.RULE);
        prooflabel2tag.put("term", ProofElementID.TERM);
        prooflabel2tag.put("formula", ProofElementID.FORMULA);
        prooflabel2tag.put("inst", ProofElementID.INSTANTIATION);
        prooflabel2tag.put("ifseqformula", ProofElementID.ASSUMES_FORMULA_IN_SEQUENT);
        prooflabel2tag.put("ifdirectformula", ProofElementID.ASSUMES_FORMULA_DIRECT);
        prooflabel2tag.put("heur", ProofElementID.RULESET);
        prooflabel2tag.put("builtin", ProofElementID.BUILT_IN_RULE);
        prooflabel2tag.put("keyLog", ProofElementID.KeY_LOG);
        prooflabel2tag.put("keyUser", ProofElementID.KeY_USER);
        prooflabel2tag.put("keyVersion", ProofElementID.KeY_VERSION);
        prooflabel2tag.put("keySettings", ProofElementID.KeY_SETTINGS);
        prooflabel2tag.put("contract", ProofElementID.CONTRACT);
        prooflabel2tag.put("ifInst", ProofElementID.ASSUMES_INST_BUILT_IN);
        prooflabel2tag.put("userinteraction", ProofElementID.USER_INTERACTION);
        prooflabel2tag.put("proofscript", ProofElementID.PROOF_SCRIPT);
        prooflabel2tag.put("newnames", ProofElementID.NEW_NAMES);
        prooflabel2tag.put("autoModeTime", ProofElementID.AUTOMODE_TIME);
        prooflabel2tag.put("mergeProc", ProofElementID.MERGE_PROCEDURE);
        prooflabel2tag.put("abstractionPredicates", ProofElementID.MERGE_ABSTRACTION_PREDICATES);
        prooflabel2tag.put("latticeType", ProofElementID.MERGE_PREDICATE_ABSTRACTION_LATTICE_TYPE);
        prooflabel2tag.put("nrMergePartners", ProofElementID.NUMBER_MERGE_PARTNERS);
        prooflabel2tag.put("distFormula", ProofElementID.MERGE_DIST_FORMULA);
        prooflabel2tag.put("mergeNode", ProofElementID.MERGE_NODE);
        prooflabel2tag.put("mergeId", ProofElementID.MERGE_ID);
        prooflabel2tag.put("userChoices", ProofElementID.MERGE_USER_CHOICES);
        prooflabel2tag.put("opengoal", IProofFileParser.ProofElementID.OPEN_GOAL);
    }

    private NamespaceSet nss;
    private Namespace<SchemaVariable> schemaVariablesNamespace;
    private HashMap<String, String> category2Default = new LinkedHashMap<>();
    private boolean onlyWith = false;
    private ImmutableSet<Choice> activatedChoices = DefaultImmutableSet.<Choice>nil();
    private HashSet usedChoiceCategories = new LinkedHashSet();
    private HashMap taclet2Builder;
    private AbbrevMap scm;


    private String filename;

    // these variables are set if a file is read in step by
    // step. This used when reading in LDTs because of cyclic
    // dependencies.
    private boolean skip_schemavariables;
    private boolean skip_functions;
    private boolean skip_transformers;
    private boolean skip_predicates;
    private boolean skip_sorts;
    private boolean skip_rulesets;
    private boolean skip_taclets;
    private boolean parse_includes = false;
    private Includes includes = new Includes();

    private boolean schemaMode = false;
    private ParserMode parserMode;

    private String chooseContract = null;
    private String proofObligation = null;
    private String problemHeader = null;

    private int savedGuessing = -1;

    /*
     counter variable for parser rules accessterm and heap_selection suffix:
     - stores nesting depth of alpha::select(heap,o,f)-terms created via pretty syntax	(i.e. terms of the form: o.f)
     - rule accessterm increases the counter
     - rule heap_selection_suffix calls method heapSelectionSuffix(), which resets
       the counter
     - In case a term similar to o.f1.f2.f3.f4 would occur, this variable should have a value of 4.
       The non-pretty syntax of this term would look similar to the following:
           T::select(h, T::select(h, T::select(h, T::select(h, o, f1) , f2) , f3), f4)
    */
    protected int globalSelectNestingDepth = 0;

    private int lineOffset = 0;
    private int colOffset = 0;
    private int stringLiteralLine = 0; // HACK!

    private Services services;
    private JavaReader javaReader;

    // if this is used then we can capture parts of the input for later use
    private IProgramMethod pm = null;

    private LinkedHashMap<RuleKey, Taclet> taclets = new LinkedHashMap<RuleKey, Taclet>();

    private ImmutableList<Contract> contracts = ImmutableSLList.nil();
    private ImmutableSet<ClassInvariant> invs = DefaultImmutableSet.<ClassInvariant>nil();

    private ParserConfig schemaConfig;
    private ParserConfig normalConfig;

    // the current active config
    private ParserConfig parserConfig;

    private Term quantifiedArrayGuard = null;

    private String profileName;

    private TokenStream lexer;
    private org.antlr.runtime.TokenStream input = null;
    private ParsableVariable selfVar;
    private boolean checkSort;
    private SchemaVariableModifierSet mods;

    /**
     * Although the parser mode can be deduced from the particular constructor
     * used we still require the caller to provide the parser mode explicitly,
     * so that the code is readable.
     */

    public Builder(ParserMode mode, TokenStream lexer, Services services) {
        this(mode, lexer);
    }

    /* Most general constructor, should only be used internally */
    private Builder(TokenStream lexer,
                    Services services,
                    NamespaceSet nss,
                    ParserMode mode) {
        this.lexer = lexer;
        this.parserMode = mode;
        this.services = services;
        this.nss = nss;
        this.schemaVariablesNamespace = new Namespace<>();
        if (this.isTacletParser()) {
            switchToSchemaMode();
        } else {
            switchToNormalMode();
        }
    }

    /**
     * Used to construct Term parser - for first-order terms
     * and formulae.
     */
    public Builder(ParserMode mode,
                   TokenStream lexer,
                   JavaReader jr,
                   Services services,
                   NamespaceSet nss,
                   AbbrevMap scm) {
        this(lexer, services, nss, mode);
        this.javaReader = jr;
        this.scm = scm;
    }


    /**
     * ONLY FOR TEST CASES.
     * Used to construct Global Declaration Term parser - for first-order
     * terms and formulae. Variables in quantifiers are expected to be
     * declared globally in the variable namespace.  This parser is used
     * for test cases, where you want to know in advance which objects
     * will represent bound variables.
     */
    public Builder(ParserMode mode,
                   TokenStream lexer,
                   Services services,
                   NamespaceSet nss) {
        this(mode,
                lexer,
                new SchemaRecoder2KeY(services, nss),
                services,
                nss,
                new LinkedHashMap());
    }

    /**
     * Used to construct Taclet parser
     */
    public Builder(ParserMode mode,
                   TokenStream lexer,
                   SchemaJavaReader jr,
                   Services services,
                   NamespaceSet nss,
                   HashMap taclet2Builder) {
        this(lexer, services, nss, mode);
        switchToSchemaMode();
        this.scm = new AbbrevMap();
        this.javaReader = jr;
        this.taclet2Builder = taclet2Builder;
    }


    /**
     * Used to construct Problem parser
     */
    public Builder(ParserMode mode,
                   TokenStream lexer,
                   ParserConfig schemaConfig,
                   ParserConfig normalConfig,
                   HashMap taclet2Builder,
                   ImmutableList<Taclet> taclets) {
        this(lexer, null, null, mode);
        if (normalConfig != null)
            scm = new AbbrevMap();
        this.schemaConfig = schemaConfig;
        this.normalConfig = normalConfig;
        switchToNormalMode();
        this.taclet2Builder = taclet2Builder;

        if (taclets != null && !taclets.isEmpty()) {
            for (Taclet t : taclets) {
                this.taclets.put(new RuleKey(t), t);
            }
        }

    }

    public Builder(ParserMode mode, TokenStream lexer) {
        this(lexer, null, null, mode);
        scm = new AbbrevMap();
        this.schemaConfig = null;
        this.normalConfig = null;
        switchToNormalMode();
        this.taclet2Builder = null;
        this.taclets = new LinkedHashMap<RuleKey, Taclet>();
    }

    public String getSourceName() {
        return filename;
    }

    public String getChooseContract() {
        return chooseContract;
    }

    public String getProofObligation() {
        return proofObligation;
    }

    public String getProblemHeader() {
        return problemHeader;
    }

    public String getProfileName() {
        return profileName;
    }

    private boolean isDeclParser() {
        return parserMode == ParserMode.DECLARATION;
    }

    private boolean isTermParser() {
        return parserMode == ParserMode.TERM;
    }

    private boolean isGlobalDeclTermParser() {
        return parserMode == ParserMode.GLOBALDECL;
    }

    private boolean isTacletParser() {
        return parserMode == ParserMode.TACLET;
    }

    private boolean isProblemParser() {
        return parserMode == ParserMode.PROBLEM;
    }

    public void raiseException(RecognitionException ex) throws RecognitionException {
        throw ex;
    }

    public ImmutableSet<Choice> getActivatedChoices() {
        return activatedChoices;
    }

    public int getLine() {
        return 0;
    }

    public int getColumn() {
        return 0;
    }

    public Includes getIncludes() {
        return includes;
    }

    public JavaInfo getJavaInfo() {
        if (isProblemParser())
            return parserConfig.javaInfo();
        if (getServices() != null)
            return getServices().getJavaInfo();
        else
            return null;
    }

    public Services getServices() {
        if (isProblemParser())
            return parserConfig.services();
        return services;
    }

    public TermFactory getTermFactory() {
        return getServices().getTermFactory();
    }

    public NamespaceSet namespaces() {
        if (isProblemParser())
            return parserConfig.namespaces();
        return nss;
    }

    private Namespace<Sort> sorts() {
        return namespaces().sorts();
    }

    private Namespace<Function> functions() {
        return namespaces().functions();
    }

    private Namespace<RuleSet> ruleSets() {
        return namespaces().ruleSets();
    }

    private Namespace<QuantifiableVariable> variables() {
        return namespaces().variables();
    }

    private Namespace<IProgramVariable> programVariables() {
        return namespaces().programVariables();
    }

    private Namespace<Choice> choices() {
        return namespaces().choices();
    }

    public Namespace<SchemaVariable> schemaVariables() {
        return schemaVariablesNamespace;
    }

    public void setSchemaVariablesNamespace(Namespace<SchemaVariable> ns) {
        this.schemaVariablesNamespace = ns;
    }

    public ImmutableList<Taclet> getTaclets() {
        ImmutableList<Taclet> result = ImmutableSLList.<Taclet>nil();

        /* maintain correct order for taclet lemma proofs */
        for (Taclet t : taclets.values()) {
            result = result.prepend(t);
        }

        // restore the order
        result = result.reverse();

        return result;
    }

    public ImmutableSet<Contract> getContracts() {
        return DefaultImmutableSet.fromImmutableList(contracts);
    }

    public ImmutableSet<ClassInvariant> getInvariants() {
        return invs;
    }

    public HashMap<String, String> getCategory2Default() {
        return category2Default;
    }

    private boolean inSchemaMode() {
        if (isTermParser() && schemaMode)
            Debug.fail("In Term parser mode schemaMode cannot be true.");
        if (isTacletParser() && !schemaMode)
            Debug.fail("In Taclet parser mode schemaMode should always be true.");
        return schemaMode;
    }

    private void switchToSchemaMode() {
        if (!isTermParser()) {
            schemaMode = true;
            if (isProblemParser())
                parserConfig = schemaConfig;
        }
    }

    private void switchToNormalMode() {
        if (!isTermParser() && !isTacletParser()) {
            schemaMode = false;
            if (isProblemParser())
                parserConfig = normalConfig;
        }
    }

    private void resetSkips() {
        skip_schemavariables = false;
        skip_functions = false;
        skip_transformers = false;
        skip_predicates = false;
        skip_sorts = false;
        skip_rulesets = false;
        skip_taclets = false;
    }

    private void skipFuncs() {
        skip_functions = true;
    }

    private void skipTransformers() {
        skip_transformers = true;
    }

    private void skipPreds() {
        skip_predicates = true;
    }

    private void skipTaclets() {
        skip_taclets = true;
    }

    private void skipVars() {
        skip_schemavariables = true;
    }

    private void skipSorts() {
        skip_sorts = true;
    }

    private void skipRuleSets() {
        skip_rulesets = true;
    }

    private Named lookup(Name n) {
        if (isProblemParser()) {
            final Namespace[] lookups = {
                    schemaConfig.namespaces().programVariables(),
                    normalConfig.namespaces().variables(),
                    schemaConfig.namespaces().variables(),
                    normalConfig.namespaces().functions(),
                    schemaConfig.namespaces().functions(),
            };
            return doLookup(n, lookups);
        } else {
            final Namespace[] lookups = {
                    programVariables(), variables(),
                    functions()
            };
            return doLookup(n, lookups);
        }
    }

    private Named doLookup(Name n, Namespace[] lookups) {
        for (int i = 0; i < lookups.length; i++) {
            if (lookups[i].lookup(n) != null) {
                return lookups[i].lookup(n);
            }
        }
        return null;
    }

    private void addInclude(String filename, boolean relativePath, boolean ldt) {
        RuleSource source = null;
        if (relativePath) {
            filename = filename.replace('/', File.separatorChar); // Not required for Windows, but whatsoever
            filename = filename.replace('\\', File.separatorChar); // Special handling for Linux
            File parent = new File(getSourceName()).getParentFile();
            File path = new File(parent, filename);
            source = RuleSourceFactory.initRuleFile(path);
        } else {
            source = RuleSourceFactory.fromDefaultLocation(filename + ".key");
        }
        if (ldt) {
            includes.putLDT(filename, source);
        } else {
            includes.put(filename, source);
        }
    }

    private void schema_var_decl(String name,
                                 Sort s,
                                 boolean makeVariableSV,
                                 boolean makeSkolemTermSV,
                                 boolean makeTermLabelSV,
                                 SchemaVariableModifierSet mods)
            throws AmbigiousDeclException {
        if (!skip_schemavariables) {
            SchemaVariable v;
            if (s == Sort.FORMULA && !makeSkolemTermSV) {
                v = SchemaVariableFactory.createFormulaSV(new Name(name),
                        mods.rigid());
            } else if (s == Sort.UPDATE) {
                v = SchemaVariableFactory.createUpdateSV(new Name(name));
            } else if (s instanceof ProgramSVSort) {
                v = SchemaVariableFactory.createProgramSV(
                        new ProgramElementName(name),
                        (ProgramSVSort) s,
                        mods.list());
            } else {
                if (makeVariableSV) {
                    v = SchemaVariableFactory.createVariableSV
                            (new Name(name), s);
                } else if (makeSkolemTermSV) {
                    v = SchemaVariableFactory.createSkolemTermSV(new Name(name),
                            s);
                } else if (makeTermLabelSV) {
                    v = SchemaVariableFactory.createTermLabelSV(new Name(name));
                } else {
                    v = SchemaVariableFactory.createTermSV(
                            new Name(name),
                            s,
                            mods.rigid(),
                            mods.strict());
                }
            }

            if (inSchemaMode()) {
                if (variables().lookup(v.name()) != null ||
                        schemaVariables().lookup(v.name()) != null) {
                    throw new AmbigiousDeclException(v.name().toString(),
                            getSourceName(),
                            getLine(),
                            getColumn());
                }
                schemaVariables().add(v);
            }
        }
    }

    private Term toZNotation(String number, Namespace<Function> functions) {
        String s = number;
        final boolean negative = (s.charAt(0) == '-');
        if (negative) {
            s = number.substring(1, s.length());
        }
        if (s.startsWith("0x")) {
            try {
                BigInteger bi = new BigInteger(s.substring(2), 16);
                s = bi.toString();
            } catch (NumberFormatException nfe) {
                Debug.fail("Not a hexadecimal constant (BTW, this should not have happened).");
            }
        }
        Term result = getTermFactory().createTerm((Function) functions.lookup(new Name("#")));

        for (int i = 0; i < s.length(); i++) {
            result = getTermFactory().createTerm((Function) functions.lookup(new Name(s.substring(i, i + 1))), result);
        }

        if (negative) {
            result = getTermFactory().createTerm((Function) functions.lookup(new Name("neglit")), result);
        }
        return getTermFactory().createTerm
                ((Function) functions.lookup(new Name("Z")), result);
    }

    private String getTypeList(ImmutableList<ProgramVariable> vars) {
        StringBuffer result = new StringBuffer("");
        final Iterator<ProgramVariable> it = vars.iterator();
        while (it.hasNext()) {
            result.append(it.next().getContainerType().getFullName());
            if (it.hasNext()) result.append(", ");
        }
        return result.toString();
    }

    private Operator getAttributeInPrefixSort(Sort prefixSort, String attributeName)
            throws RecognitionException, NotDeclException/*SemanticException*/ {
        final JavaInfo javaInfo = getJavaInfo();

        Operator result = null;

        if (inSchemaMode()) {
            // if we are currently reading taclets we look for schema variables first
            result = schemaVariables().lookup(new Name(attributeName));
        }

        assert inSchemaMode() || result == null;
        if (result == null) {

            final boolean unambigousAttributeName = attributeName.indexOf(':') != -1;

            if (unambigousAttributeName) {
                result = javaInfo.getAttribute(attributeName);
            } else if (inSchemaMode() && attributeName.equals("length")) {
                try {
                    result = javaInfo.getArrayLength();
                } catch (Exception ex) {
                    throwEx(new KeYSemanticException(input, getSourceName(), ex));
                }
            } else if (attributeName.equals("<inv>")) {
                // The invariant observer "<inv>" is implicit and
                // not part of the class declaration
                // A special case is needed, hence.
                result = javaInfo.getInvProgramVar();
            } else {
                if (inSchemaMode()) {
                    semanticError("Either undeclared schema variable '" +
                            attributeName + "' or a not fully qualified attribute in taclet.");
                }
                final KeYJavaType prefixKJT = javaInfo.getKeYJavaType(prefixSort);
                if (prefixKJT == null) {
                    semanticError("Could not find type '" + prefixSort + "'. Maybe mispelled or " +
                            "you use an array or object type in a .key-file with missing " +
                            "\\javaSource section.");
                }
                // WATCHOUT why not in DECLARATION MODE
                if (!isDeclParser()) {
                    ProgramVariable var = javaInfo.getCanonicalFieldProgramVariable(attributeName, prefixKJT);
                    if (var == null) {
                        LogicVariable logicalvar = (LogicVariable) namespaces().variables().lookup(attributeName);
                        if (logicalvar == null) {
                            semanticError("There is no attribute '" + attributeName +
                                    "' declared in type '" + prefixSort + "' and no logical variable of that name.");
                        } else {
                            result = logicalvar;
                        }
                    } else {
                        result = var;
                    }
                }
            }
        }

        if (result == null && !("length".equals(attributeName))) {
            throw new NotDeclException(input, "Attribute ", attributeName);
        }
        return result;
    }


    public Term createAttributeTerm(Term prefix,
                                    Operator attribute) throws RecognitionException/*SemanticException*/ {
        Term result = prefix;

        if (attribute instanceof SchemaVariable) {
            if (!inSchemaMode()) {
                semanticError("Schemavariables may only occur inside taclets.");
            }
            SchemaVariable sv = (SchemaVariable) attribute;
            if (sv.sort() instanceof ProgramSVSort
                    || sv.sort() == AbstractTermTransformer.METASORT) {
                semanticError("Cannot use schema variable " + sv + " as an attribute");
            }
            result = getServices().getTermBuilder().select(sv.sort(),
                    getServices().getTermBuilder().getBaseHeap(),
                    prefix,
                    getTermFactory().createTerm(attribute));
        } else {
            if (attribute instanceof LogicVariable) {
                Term attrTerm = getTermFactory().createTerm(attribute);
                result = getServices().getTermBuilder().dot(Sort.ANY, result, attrTerm);
            } else if (attribute instanceof ProgramConstant) {
                result = getTermFactory().createTerm(attribute);
            } else if (attribute == getServices().getJavaInfo().getArrayLength()) {
                result = getServices().getTermBuilder().dotLength(result);
            } else {
                ProgramVariable pv = (ProgramVariable) attribute;
                Function fieldSymbol
                        = getServices().getTypeConverter()
                        .getHeapLDT()
                        .getFieldSymbolForPV((LocationVariable) pv,
                                getServices());
                if (pv.isStatic()) {
                    result = getServices().getTermBuilder().staticDot(pv.sort(), fieldSymbol);
                } else {
                    result = getServices().getTermBuilder().dot(pv.sort(), result, fieldSymbol);
                }
            }
        }
        return result;
    }

    private LogicVariable bindVar(String id, Sort s) {
        if (isGlobalDeclTermParser())
            Debug.fail("bindVar was called in Global Declaration Term parser.");
        LogicVariable v = new LogicVariable(new Name(id), s);
        namespaces().setVariables(variables().extended(v));
        return v;
    }

    private void bindVar(LogicVariable v) {
        if (isGlobalDeclTermParser())
            Debug.fail("bindVar was called in Global Declaration Term parser.");
        namespaces().setVariables(variables().extended(v));
    }

    private void bindVar() {
        if (isGlobalDeclTermParser())
            Debug.fail("bindVar was called in Global Declaration Term parser.");
        namespaces().setVariables(new Namespace(variables()));
    }

    private KeYJavaType getTypeByClassName(String s)
            throws RecognitionException/*KeYSemanticException*/ {
        KeYJavaType kjt = null;
        try {
            kjt = getJavaInfo().getTypeByClassName(s, null);
        } catch (RuntimeException e) {
            return null;
        }

        return kjt;
    }

    private boolean isPackage(String name) {
        try {
            return getJavaInfo().isPackage(name);
        } catch (RuntimeException e) {
            // may be thrown in cases of invalid java identifiers
            return false;
        }
    }

    protected boolean isHeapTerm(Term term) {
        return term != null && term.sort() ==
                getServices().getTypeConverter().getHeapLDT().targetSort();
    }

    private boolean isSequenceTerm(Term reference) {
        return reference != null && reference.sort().name().equals(SeqLDT.NAME);
    }

    private boolean isIntTerm(Term reference) {
        return reference.sort().name().equals(IntegerLDT.NAME);
    }

    private void unbindVars(Namespace<QuantifiableVariable> orig) {
        if (isGlobalDeclTermParser()) {
            Debug.fail("unbindVars was called in Global Declaration Term parser.");
        }
        namespaces().setVariables(orig);
    }


    private Set progVars(JavaBlock jb) {
        if (isGlobalDeclTermParser()) {
            ProgramVariableCollector pvc
                    = new ProgramVariableCollector(jb.program(), getServices());
            pvc.start();
            return pvc.result();
        } else if (!isDeclParser()) {
            if ((isTermParser() || isProblemParser()) && jb.isEmpty()) {
                return new LinkedHashSet();
            }
            DeclarationProgramVariableCollector pvc
                    = new DeclarationProgramVariableCollector(jb.program(), getServices());
            pvc.start();
            return pvc.result();
        }
        Debug.fail("KeYParser.progVars(): this statement should not be reachable.");
        return null;
    }

    private Term termForParsedVariable(ParsableVariable v)
            throws RecognitionException/*SemanticException*/ {
        if (v instanceof LogicVariable || v instanceof ProgramVariable) {
            return getTermFactory().createTerm(v);
        } else {
            if (isGlobalDeclTermParser())
                semanticError(v + " is not a logic variable");
            if (isTermParser())
                semanticError(v + " is an unknown kind of variable.");
            if (inSchemaMode() && v instanceof SchemaVariable) {
                return getTermFactory().createTerm(v);
            } else {
                String errorMessage = "";
                if (inSchemaMode()) {
                    errorMessage += v + " is not a program, logic or schema variable";
                } else {
                    errorMessage += v + " is not a logic or program variable";
                }
                semanticError(errorMessage);
            }
        }
        return null;
    }

    private PairOfStringAndJavaBlock getJavaBlock(Token t) throws RecognitionException/*SemanticException*/ {
        PairOfStringAndJavaBlock sjb = new PairOfStringAndJavaBlock();
        String s = t.getText();
        int index = s.indexOf("\n");
        sjb.opName = s.substring(0, index);
        s = s.substring(index + 1);
        Debug.out("Modal operator name passed to getJavaBlock: ", sjb.opName);
        Debug.out("Java block passed to getJavaBlock: ", s);

        JavaReader jr = javaReader;
        String input = "";

        try {
            if (inSchemaMode()) {
                if (isProblemParser()) // Alt jr==null;
                    jr = new SchemaRecoder2KeY(parserConfig.services(),
                            parserConfig.namespaces());
                ((SchemaJavaReader) jr).setSVNamespace(schemaVariables());
            } else {
                if (isProblemParser()) // Alt jr==null;
                    jr = new Recoder2KeY(parserConfig.services(),
                            parserConfig.namespaces());
            }

            if (inSchemaMode() || isGlobalDeclTermParser()) {
                sjb.javaBlock = jr.readBlockWithEmptyContext(s);
            } else {
                sjb.javaBlock = jr.readBlockWithProgramVariables(programVariables(), s);
            }
        } catch (de.uka.ilkd.key.java.PosConvertException e) {
            lineOffset = e.getLine() - 1;
            colOffset = e.getColumn() + 1;
            throw new RecognitionException(input);
            //throw new JavaParserException(e.getMessage(), t.getText(),
            //    getSourceName(), t.getLine(), t.getCharPositionInLine(), lineOffset, colOffset);
        } catch (de.uka.ilkd.key.java.ConvertException e) {
            if (e.parseException() != null
                    && e.parseException().currentToken != null
                    && e.parseException().currentToken.next != null) {
                lineOffset = e.parseException().currentToken.next.beginLine;
                colOffset = e.parseException().currentToken.next.beginColumn;
                e.parseException().currentToken.next.beginLine = getLine() - 1;
                e.parseException().currentToken.next.beginColumn = getColumn();
                throw new RecognitionException(input);
                //throw new JavaParserException(e.getMessage(), t.getText(), getSourceName(), t.getLine(), t.getCharPositionInLine(), -1, -1);  // row/columns already in text
            }
            if (e.proofJavaException() != null
                    && e.proofJavaException().currentToken != null
                    && e.proofJavaException().currentToken.next != null) {
                lineOffset = e.proofJavaException().currentToken.next.beginLine - 1;
                colOffset = e.proofJavaException().currentToken.next.beginColumn;
                e.proofJavaException().currentToken.next.beginLine = getLine();
                e.proofJavaException().currentToken.next.beginColumn = getColumn();
                throw new RecognitionException(input);
                //throw  new JavaParserException(e.getMessage(), t.getText(), getSourceName(), t.getLine(), t.getCharPositionInLine(), lineOffset, colOffset);

            }
            throw new RecognitionException(input);
            //throw new JavaParserException(e.getMessage(), t.getText(), getSourceName(), t.getLine(), t.getCharPositionInLine());
        }
        return sjb;
    }

    /**
     * looks up and returns the sort of the given name or null if none has been found.
     * If the sort is not found for the first time, the name is expanded with "java.lang."
     * and the look up restarts
     */
    private Sort lookupSort(String name) {
        Sort result = (Sort) sorts().lookup(new Name(name));
        if (result == null) {
            if (name.equals(NullSort.NAME.toString())) {
                Sort objectSort
                        = (Sort) sorts().lookup(new Name("java.lang.Object"));
                if (objectSort == null) {
                    semanticError("Null sort cannot be used before "
                            + "java.lang.Object is declared");
                }
                result = new NullSort(objectSort);
                sorts().add(result);
            } else {
                result = (Sort) sorts().lookup(new Name("java.lang." + name));
            }
        }
        return result;
    }


    /**
     * looks up a function, (program) variable or static query of the
     * given name varfunc_id and the argument terms args in the namespaces
     * and java info.
     *
     * @param varfunc_name the String with the symbols name
     * @param args         is null iff no argument list is given, for instance `f',
     *                     and is an array of size zero, if an empty argument list was given,
     *                     for instance `f()'.
     */
    private Operator lookupVarfuncId(String varfunc_name, Term[] args)
            throws RecognitionException, NotDeclException/*NotDeclException, SemanticException*/ {

        // case 1a: variable
        // case 1b: schema variable
        Name name = new Name(varfunc_name);
        Operator v = variables().lookup(name);
        if (v == null) {
            v = schemaVariables().lookup(name);
        }

        if (v != null && (args == null || (inSchemaMode() && v instanceof ModalOperatorSV))) {
            return v;
        }

        // case 2: program variable
        v = (Operator) programVariables().lookup
                (new ProgramElementName(varfunc_name));
        if (v != null && args == null) {
            return v;
        }

        // case 3: function
        v = (Operator) functions().lookup(new Name(varfunc_name));
        if (v != null) { // we allow both args==null (e.g. `c')
            // and args.length=0 (e.g. 'c())' here
            return v;
        }


        // case 4: instantiation of sort depending function
        int separatorIndex = varfunc_name.indexOf("::");
        if (separatorIndex > 0) {
            String sortName = varfunc_name.substring(0, separatorIndex);
            String baseName = varfunc_name.substring(separatorIndex + 2);
            Sort sort = lookupSort(sortName);
            SortDependingFunction firstInstance
                    = SortDependingFunction.getFirstInstance(new Name(baseName),
                    getServices());

            if (sort != null && firstInstance != null) {
                v = firstInstance.getInstanceFor(sort, getServices());
                if (v != null) {
                    return v;
                }
            }
        }

        // not found

        if (args == null) {
            throw new NotDeclException
                    (input, "(program) variable or constant", varfunc_name);
        } else {
            throw new NotDeclException
                    (input, "function or static query", varfunc_name);
        }
    }

    private boolean isStaticAttribute() throws RecognitionException/*KeYSemanticException*/ {
        if (inSchemaMode()) return false;
        final JavaInfo javaInfo = getJavaInfo();
        KeYJavaType kjt = null;
        boolean result = false;
//        try {
        int n = 1;
        StringBuffer className = new StringBuffer(input.LT(n).getText());
        while (isPackage(className.toString()) || input.LA(n + 2) == KeYLexer.NUM_LITERAL ||
                (input.LT(n + 2) != null && input.LT(n + 2).getText() != null &&
                        input.LT(n + 2).getText().length() > 0 && input.LT(n + 2).getText().charAt(0) <= 'Z' && input.LT(n + 2).getText().charAt(0) >= 'A' &&
                        (input.LT(n + 2).getText().length() == 1 ||
                                input.LT(n + 2).getText().charAt(1) <= 'z' && input.LT(n + 2).getText().charAt(1) >= 'a'))) {
            if (input.LA(n + 1) != KeYLexer.DOT && input.LA(n + 1) != KeYLexer.EMPTYBRACKETS) return false;
            // maybe still an attribute starting with an uppercase letter followed by a lowercase letter
            if (getTypeByClassName(className.toString()) != null) {
                ProgramVariable maybeAttr =
                        javaInfo.getAttribute(input.LT(n + 2).getText(), getTypeByClassName(className.toString()));
                if (maybeAttr != null) {
                    return true;
                }
            }
            className.append(".");
            className.append(input.LT(n + 2).getText());
            n += 2;
        }
        while (input.LA(n + 1) == KeYLexer.EMPTYBRACKETS) {
            className.append("[]");
            n++;
        }
        kjt = getTypeByClassName(className.toString());

        if (kjt != null) {
            // works as we do not have inner classes
            if (input.LA(n + 1) == KeYLexer.DOT) {
                final ProgramVariable pv =
                        javaInfo.getAttribute(input.LT(n + 2).getText(), kjt);
                result = (pv != null && pv.isStatic());
            }
        } else {
            result = false;
        }
        return result;
    }

    private boolean isTermTransformer() /*throws TokenStreamException*/ {
        if ((input.LA(1) == KeYLexer.IDENT &&
                AbstractTermTransformer.name2metaop(input.LT(1).getText()) != null)
                || input.LA(1) == KeYLexer.IN_TYPE)
            return true;
        return false;
    }

    private boolean isStaticQuery() throws RecognitionException/*KeYSemanticException*/ {
        if (inSchemaMode()) return false;
        final JavaInfo javaInfo = getJavaInfo();
        boolean result = false;
//    try {
        int n = 1;
        KeYJavaType kjt = null;
        StringBuffer className = new StringBuffer(input.LT(n).getText());
        while (isPackage(className.toString())) {
            if (input.LA(n + 1) != KeYLexer.DOT) return false;
            className.append(".");
            className.append(input.LT(n + 2).getText());
            n += 2;
        }
        kjt = getTypeByClassName(className.toString());
        if (kjt != null) {
            if (input.LA(n + 1) == KeYLexer.DOT && input.LA(n + 3) == KeYLexer.LPAREN) {
                Iterator<IProgramMethod> it = javaInfo.getAllProgramMethods(kjt).iterator();
                while (it.hasNext()) {
                    final IProgramMethod pm = it.next();
                    final String name = kjt.getFullName() + "::" + input.LT(n + 2).getText();
                    if (pm != null && pm.isStatic() && pm.name().toString().equals(name)) {
                        result = true;
                        break;
                    }
                }
            }
        }
        return result;
    }


    private TacletBuilder createTacletBuilderFor
            (Object find, int applicationRestriction)
            throws RecognitionException/*InvalidFindException*/ {
        if (applicationRestriction != RewriteTaclet.NONE &&
                applicationRestriction != RewriteTaclet.IN_SEQUENT_STATE &&
                !(find instanceof Term)) {
            String mod = "";
            if ((applicationRestriction & RewriteTaclet.SAME_UPDATE_LEVEL) != 0) {
                mod = "\"\\sameUpdateLevel\"";
            }
            if ((applicationRestriction & RewriteTaclet.ANTECEDENT_POLARITY) != 0) {
                if (mod != "") mod += " and ";
                mod += "\"\\antecedentPolarity\"";
            }
            if ((applicationRestriction & RewriteTaclet.SUCCEDENT_POLARITY) != 0) {
                if (mod != "") mod += " and ";
                mod += "\"\\succedentPolarity\"";
            }
            if (mod == "") {
                mod = "Application restrictions";
            }

            throwEx(new InvalidFindException
                    (mod + " may only be used for rewrite taclets:" + find,
                            getSourceName(), getLine(), getColumn()));
        }
        if (find == null) {
            return new NoFindTacletBuilder();
        } else if (find instanceof Term) {
            return new RewriteTacletBuilder().setFind((Term) find)
                    .setApplicationRestriction(applicationRestriction);
        } else if (find instanceof Sequent) {
            Sequent findSeq = (Sequent) find;
            if (findSeq.isEmpty()) {
                return new NoFindTacletBuilder();
            } else if (findSeq.antecedent().size() == 1
                    && findSeq.succedent().size() == 0) {
                Term findFma = findSeq.antecedent().get(0).formula();
                AntecTacletBuilder b = new AntecTacletBuilder();
                b.setFind(findFma);
                b.setIgnoreTopLevelUpdates((applicationRestriction & RewriteTaclet.IN_SEQUENT_STATE) == 0);
                return b;
            } else if (findSeq.antecedent().size() == 0
                    && findSeq.succedent().size() == 1) {
                Term findFma = findSeq.succedent().get(0).formula();
                SuccTacletBuilder b = new SuccTacletBuilder();
                b.setFind(findFma);
                b.setIgnoreTopLevelUpdates((applicationRestriction & RewriteTaclet.IN_SEQUENT_STATE) == 0);
                return b;
            } else {
                throwEx(new InvalidFindException
                        ("Unknown find-sequent (perhaps null?):" + findSeq,
                                getSourceName(), getLine(), getColumn()));
            }
        } else {
            throwEx(new InvalidFindException
                    ("Unknown find class type: " + find.getClass().getName(),
                            getSourceName(), getLine(), getColumn()));
        }
        //TODO
    }

    private void addGoalTemplate(TacletBuilder b,
                                 String id,
                                 Object rwObj,
                                 Sequent addSeq,
                                 ImmutableList<Taclet> addRList,
                                 ImmutableSet<SchemaVariable> pvs,
                                 ImmutableSet<Choice> soc)
            throws RecognitionException, UnfittingReplacewithException/*SemanticException*/ {
        TacletGoalTemplate gt = null;
        if (rwObj == null) {
            // there is no replacewith, so we take
            gt = new TacletGoalTemplate(addSeq,
                    addRList,
                    pvs);
        } else {
            if (b instanceof NoFindTacletBuilder) {
                // there is a replacewith without a find.
                throw new RecognitionException("");
                //new UnfittingReplacewithException
                //("Replacewith without find", getSourceName(),
                // getLine(), getColumn());
            } else if (b instanceof SuccTacletBuilder
                    || b instanceof AntecTacletBuilder) {
                if (rwObj instanceof Sequent) {
                    gt = new AntecSuccTacletGoalTemplate(addSeq,
                            addRList,
                            (Sequent) rwObj,
                            pvs);
                } else {
                    throw new UnfittingReplacewithException
                            ("Replacewith in a Antec-or SuccTaclet has " +
                                    "to contain a sequent (not a term)",
                                    getSourceName(), getLine(), getColumn());
                }
            } else if (b instanceof RewriteTacletBuilder) {
                if (rwObj instanceof Term) {
                    gt = new RewriteTacletGoalTemplate(addSeq,
                            addRList,
                            (Term) rwObj,
                            pvs);
                } else {
                    throw new UnfittingReplacewithException
                            ("Replacewith in a RewriteTaclet has " +
                                    "to contain a term (not a sequent)",
                                    getSourceName(), getLine(), getColumn());
                }
            }
        }
        gt.setName(id);
        b.addTacletGoalTemplate(gt);
        if (soc != null) b.addGoal2ChoicesMapping(gt, soc);
    }

    public void testLiteral(String l1, String l2)
            throws RecognitionException/*KeYSemanticException*/ {
        if (!l1.equals(l2)) {
            semanticError("Expecting '" + l1 + "', found '" + l2 + "'.");
        }
        ;
    }


    /**
     * returns the ProgramMethod parsed in the jml_specifications section.
     */
    public IProgramMethod getProgramMethod() {
        return pm;
    }

    public void addFunction(Function f) {
        functions().add(f);
    }

    private ImmutableSet<Modality> lookupOperatorSV(String opName, ImmutableSet<Modality> modalities)
            throws RecognitionException/*KeYSemanticException*/ {
        SchemaVariable sv = schemaVariables().lookup(new Name(opName));
        if (sv == null || !(sv instanceof ModalOperatorSV)) {
            semanticError("Schema variable " + opName + " not defined.");
        }
        ModalOperatorSV osv = (ModalOperatorSV) sv;
        modalities = modalities.union(osv.getModalities());
        return modalities;
    }

    private ImmutableSet<Modality> opSVHelper(String opName,
                                              ImmutableSet<Modality> modalities)
            throws RecognitionException/*KeYSemanticException*/ {
        if (opName.charAt(0) == '#') {
            return lookupOperatorSV(opName, modalities);
        } else {
            switchToNormalMode();
            Modality m = Modality.getModality(opName);
            switchToSchemaMode();
            if (m == null) {
                semanticError("Unrecognised operator: " + opName);
            }
            modalities = modalities.add(m);
        }
        return modalities;
    }

    protected void semanticError(String message) {
        throwEx(new KeYSemanticException(input, getSourceName(), message));
    }

    private static class PairOfStringAndJavaBlock {
        String opName;
        JavaBlock javaBlock;
    }

    private static boolean isSelectTerm(Term term) {
        return term.op().name().toString().endsWith("::select") && term.arity() == 3;
    }

    private boolean isImplicitHeap(Term t) {
        return getServices().getTermBuilder().getBaseHeap().equals(t);
    }

    // This is used for testing in TestTermParserHeap.java
    public static final String NO_HEAP_EXPRESSION_BEFORE_AT_EXCEPTION_MESSAGE
            = "Expecting select term before '@', not: ";

    private Term replaceHeap(Term term, Term heap, int depth) throws RecognitionException, KeYSemanticException {
        if (depth > 0) {

            if (isSelectTerm(term)) {

                if (!isImplicitHeap(term.sub(0))) {
                    semanticError("Expecting program variable heap as first argument of: " + term);
                }

                Term[] params = new Term[]{heap, replaceHeap(term.sub(1), heap, depth - 1), term.sub(2)};
                return (getServices().getTermFactory().createTerm(term.op(), params));

            } else if (term.op() instanceof ObserverFunction) {
                if (!isImplicitHeap(term.sub(0))) {
                    semanticError("Expecting program variable heap as first argument of: " + term);
                }

                Term[] params = new Term[term.arity()];
                params[0] = heap;
                params[1] = replaceHeap(term.sub(1), heap, depth - 1);
                for (int i = 2; i < params.length; i++) {
                    params[i] = term.sub(i);
                }

                return (getServices().getTermFactory().createTerm(term.op(), params));

            } else {
                semanticError(NO_HEAP_EXPRESSION_BEFORE_AT_EXCEPTION_MESSAGE + term);
                throw new RecognitionException();
            }

        } else {
            return term;
        }
    }

    /*
     * Replace standard heap by another heap in an observer function.
     */
    protected Term heapSelectionSuffix(Term term, Term heap) throws RecognitionException, KeYSemanticException {

        if (!isHeapTerm(heap)) {
            semanticError("Expecting term of type Heap but sort is " + heap.sort()
                    + " for term: " + term);
        }

        Term result = replaceHeap(term, heap, globalSelectNestingDepth);

        // reset globalSelectNestingDepth
        globalSelectNestingDepth = 0;

        return result;
    }

    private String unescapeString(String string) {
        char[] chars = string.toCharArray();
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < chars.length; i++) {
            if (chars[i] == '\\' && i < chars.length - 1) {
                switch (chars[++i]) {
                    case 'n':
                        sb.append("\n");
                        break;
                    case 'f':
                        sb.append("\f");
                        break;
                    case 'r':
                        sb.append("\r");
                        break;
                    case 't':
                        sb.append("\t");
                        break;
                    case 'b':
                        sb.append("\b");
                        break;
                    case ':':
                        sb.append("\\:");
                        break; // this is so in KeY ...
                    default:
                        sb.append(chars[i]);
                        break; // this more relaxed than before, \a becomes a ...
                }
            } else {
                sb.append(chars[i]);
            }
        }
        return sb.toString();
    }

    @Override
    public Object visitFile(KeYParser.FileContext ctx) {
        return super.visitFile(ctx);
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        return super.visitDecls(ctx);
    }

    boolean ldt = false;

    @Override
    public Object visitOne_include_statement(KeYParser.One_include_statementContext ctx) {
        if (ctx.INCLUDE() != null) ldt = false;
        if (ctx.INCLUDELDTS() != null) ldt = false;
        ctx.one_include().forEach(it -> it.accept(this));
        return null;
    }

    @Override
    public Object visitOne_include(KeYParser.One_includeContext ctx) {
        if (parse_includes) return null;

        if (ctx.absfile != null) {
            addInclude(ctx.absfile.getText(), false, ldt);
        }
        if (ctx.relfile != null) {
            addInclude(ctx.relfile.getText(), true, ldt);
        }
        return null;
    }

    @Override
    public Object visitOptions_choice(KeYParser.Options_choiceContext ctx) {
        return super.visitOptions_choice(ctx);
    }

    @Override
    public Object visitActivated_choice(KeYParser.Activated_choiceContext ctx) {
        var cat = ctx.cat.getText();
        var ch = ctx.choice_.getText();
        if (usedChoiceCategories.contains(cat)) {
            throw new IllegalArgumentException("You have already chosen a different option for " + cat);
        }
        usedChoiceCategories.add(cat);
        var name = cat + ":" + ch;
        var c = (Choice) choices().lookup(new Name(name));
        if (c == null) {
            throwEx(new NotDeclException(input, "Option", ch));
        } else {
            activatedChoices = activatedChoices.add(c);
        }
        return null;
    }

    @Override
    public Object visitOption_decls(KeYParser.Option_declsContext ctx) {
        return super.visitOption_decls(ctx);
    }


    @Override
    public Object visitChoice(KeYParser.ChoiceContext ctx) {
        String cat = ctx.category.getText();
        for (KeYParser.Choice_optionContext catctx : ctx.choice_option()) {
            var name = cat + ":" + catctx.choice_.getText();
            Choice c = choices().lookup(new Name(name));
            if (c == null) {
                c = new Choice(catctx.choice_.getText(), cat);
                choices().add(c);
            }
            if (!category2Default.containsKey(cat)) {
                category2Default.put(cat, name);
            }
        }
        if (!category2Default.containsKey(cat)) {
            choices().add(new Choice("On", cat));
            choices().add(new Choice("Off", cat));
            category2Default.put(cat, cat + ":On");
        }
        return null;
    }

    @Override
    public Object visitChoice_option(KeYParser.Choice_optionContext ctx) {
        return super.visitChoice_option(ctx);
    }

    @Override
    public Object visitSort_decls(KeYParser.Sort_declsContext ctx) {
        ImmutableList<Sort> lsorts = ImmutableSLList.nil();
        //TODO multipleSorts = ImmutableSLList.<Sort>nil();
        for (KeYParser.One_sort_declContext c : ctx.one_sort_decl()) {
            c.accept(this);
        }
        return null;
    }

    @Override
    public Object visitOne_sort_decl_generic(KeYParser.One_sort_decl_genericContext ctx) {
        boolean isGenericSort = true;
        ImmutableSLList<String> sortIds = (ImmutableSLList<String>) ctx.sortIds.accept(this);
        Sort[] sortOneOf =
                ctx.sortOneOf != null
                        ? (Sort[]) ctx.sortOneOf.accept(this)
                        : new Sort[0];
        Sort[] sortExt =
                ctx.sortExt != null
                        ? (Sort[]) ctx.sortExt.accept(this)
                        : new Sort[0];
        //TODO
    }

    @Override
    public Object visitOne_sort_decl_proxy(KeYParser.One_sort_decl_proxyContext ctx) {
        boolean isProxySort = true;
        ImmutableSLList<String> sortIds = (ImmutableSLList<String>) ctx.sortIds.accept(this);
        Sort[] sortExt =
                ctx.sortExt != null
                        ? (Sort[]) ctx.sortExt.accept(this)
                        : new Sort[0];
        //TODO
    }

    @Override
    public Object visitOne_sort_decl_default(KeYParser.One_sort_decl_defaultContext ctx) {
        boolean isAbstractSort = ctx.ABSTRACT() != null;
        Sort[] sortExt =
                ctx.sortExt != null
                        ? (Sort[]) ctx.sortExt.accept(this)
                        : new Sort[0];

        List<String> sortIds = ctx.COMMA() != null
                ? (List<String>) ctx.sortIds.accept(this)
                : new LinkedList<>();
        sortIds.add(0, (String) ctx.firstSort.accept(this));
        return createSort(isAbstractSort, false, false, sortExt, new Sort[0], sortIds);
    }

    private List<Sort> createSort(boolean isAbstractSort, boolean isGenericSort, boolean isProxySort,
                                  Sort[] sortExt, Sort[] sortOneOf, List<String> sortIds) {
        List<Sort> createdSorts = new ArrayList<>(5);
        if (!skip_sorts) {
            for (String sortId : sortIds) {
                Name sort_name = new Name(sortId);
                // attention: no expand to java.lang here!
                if (sorts().lookup(sort_name) == null) {
                    Sort s = null;
                    if (isGenericSort) {
                        int i;
                        ImmutableSet<Sort> ext = DefaultImmutableSet.<Sort>nil();
                        ImmutableSet<Sort> oneOf = DefaultImmutableSet.<Sort>nil();

                        for (i = 0; i != sortExt.length; ++i)
                            ext = ext.add(sortExt[i]);

                        for (i = 0; i != sortOneOf.length; ++i)
                            oneOf = oneOf.add(sortOneOf[i]);

                        try {
                            s = new GenericSort(sort_name, ext, oneOf);
                        } catch (GenericSupersortException e) {
                            throwEx(new GenericSortException("sort", "Illegal sort given",
                                    e.getIllegalSort(), getSourceName(), getLine(), getColumn()));
                        }
                    } else if (new Name("any").equals(sort_name)) {
                        s = Sort.ANY;
                    } else {
                        ImmutableSet<Sort> ext = DefaultImmutableSet.<Sort>nil();

                        for (int i = 0; i != sortExt.length; ++i) {
                            ext = ext.add(sortExt[i]);
                        }

                        if (isProxySort) {
                            s = new ProxySort(sort_name, ext);
                        } else {
                            s = new SortImpl(sort_name, ext, isAbstractSort);
                        }
                    }
                    assert s != null;
                    sorts().add(s);
                    createdSorts.add(s);
                }
            }
        }
        return createdSorts;
    }

    private void throwEx(Throwable e) {
        throw new RuntimeException(e);
    }

    @Override
    public String visitSimple_ident_dots(KeYParser.Simple_ident_dotsContext ctx) {
        return ctx.getText();
    }

    @Override
    public List<Sort> visitExtends_sorts(KeYParser.Extends_sortsContext ctx) {
        return mapOf(ctx.any_sortId_check());
    }

    public <T> List<T> mapOf(List<? extends ParserRuleContext> seq) {
        return seq.stream().map(it -> (T) it.accept(this))
                .collect(Collectors.toList());
    }

    @Override
    public List<Sort> visitOneof_sorts(KeYParser.Oneof_sortsContext ctx) {
        return mapOf(ctx.sortId_check());
    }

    @Override
    public KeYJavaType visitKeyjavatype(KeYParser.KeyjavatypeContext ctx) {
        boolean array = false;
        var type = visitSimple_ident_dots(ctx.simple_ident_dots());
        for (int i = 0; i < ctx.EMPTYBRACKETS().size(); i++) {
            array = true;
            type += "[]";
        }
        var kjt = getJavaInfo().getKeYJavaType(type);

        //expand to "java.lang"
        if (kjt == null) {
            try {
                String guess = "java.lang." + type;
                kjt = getJavaInfo().getKeYJavaType(guess);
            } catch (Exception e) {
                kjt = null;
            }
        }

        //arrays
        if (kjt == null && array) {
            try {
                JavaBlock jb = getJavaInfo().readJavaBlock("{" + type + " k;}");
                kjt = ((VariableDeclaration)
                        ((StatementBlock) jb.program()).getChildAt(0)).
                        getTypeReference().getKeYJavaType();
            } catch (Exception e) {
                kjt = null;
            }
        }

        //try as sort without Java type (neede e.g. for "Heap")
        if (kjt == null) {
            Sort sort = lookupSort(type);
            if (sort != null) {
                kjt = new KeYJavaType(null, sort);
            }
        }

        if (kjt == null) {
            semanticError("Unknown type: " + type);
        }

        return kjt;
    }

    @Override
    public Object visitProg_var_decls(KeYParser.Prog_var_declsContext ctx) {
        String var_name;

        for (int i = 0; i < ctx.simple_ident_comma_list().size(); i++) {
            var var_names = (List<String>) visit(ctx.simple_ident_comma_list(i));
            var kjt = (KeYJavaType) visit(ctx.keyjavatype(i));
            for (String varName : var_names) {
                var_name = varName;
                ProgramElementName pvName = new ProgramElementName(var_name);
                Named name = lookup(pvName);
                if (name != null) {
                    // commented out as pv do not have unique name (at the moment)
                    //  throw new AmbigiousDeclException
                    //  	(var_name, getSourceName(), getLine(), getColumn());
                    if (!(name instanceof ProgramVariable) || (name instanceof ProgramVariable &&
                            !((ProgramVariable) name).getKeYJavaType().equals(kjt))) {
                        namespaces().programVariables().add(new LocationVariable
                                (pvName, kjt));
                    }
                } else {
                    namespaces().programVariables().add(new LocationVariable
                            (pvName, kjt));
                }
            }
        }
        return null;
    }

    @Override
    public String visitString_literal(KeYParser.String_literalContext ctx) {
        var lit = unescapeString(ctx.id.getText());
        lit = lit.substring(1, lit.length() - 1);
        return lit;
    }

    @Override
    public String visitSimple_ident(KeYParser.Simple_identContext ctx) {
        return ctx.IDENT().getText();
    }

    @Override
    public List<String> visitSimple_ident_comma_list(KeYParser.Simple_ident_comma_listContext ctx) {
        return mapOf(ctx.simple_ident());
    }

    @Override
    public Object visitSchema_var_decls(KeYParser.Schema_var_declsContext ctx) {
        return super.visitSchema_var_decls(ctx);
    }

    @Override
    public Object visitOne_schema_var_decl(KeYParser.One_schema_var_declContext ctx) {
        //TODO
        /*
          boolean makeVariableSV  = false;
    boolean makeSkolemTermSV = false;
    boolean makeTermLabelSV  = false;
    SchemaVariableModifierSet mods = null;
} :
   (MODALOPERATOR one_schema_modal_op_decl SEMI)
 |
  (
   (
    PROGRAM
    { mods = new SchemaVariableModifierSet.ProgramSV (); }
    ( schema_modifiers[mods] ) ?
    id = simple_ident ( LBRACKET nameString = simple_ident EQUALS parameter = simple_ident_dots RBRACKET )? {
       if(nameString != null && !"name".equals(nameString)) {
         semanticError("Unrecognized token '"+nameString+"', expected 'name'");
       }
       ProgramSVSort psv = ProgramSVSort.name2sort().get(new Name(id));
       s = (Sort) (parameter != null ? psv.createInstance(parameter) : psv);
       if (s == null) {
         semanticError
           ("Program SchemaVariable of type "+id+" not found.");
       }
    }
    ids = simple_ident_comma_list
  | FORMULA
    { mods = new SchemaVariableModifierSet.FormulaSV (); }
    ( schema_modifiers[mods] ) ?
    {s = Sort.FORMULA;}
    ids = simple_ident_comma_list
  | TERMLABEL
    { makeTermLabelSV = true; }
    { mods = new SchemaVariableModifierSet.TermLabelSV (); }
    ( schema_modifiers[mods] ) ?
    ids = simple_ident_comma_list
  | UPDATE
    { mods = new SchemaVariableModifierSet.FormulaSV (); }
    ( schema_modifiers[mods] ) ?
    {s = Sort.UPDATE;}
    ids = simple_ident_comma_list
  | SKOLEMFORMULA
    { makeSkolemTermSV = true; }
    { mods = new SchemaVariableModifierSet.FormulaSV (); }
    ( schema_modifiers[mods] ) ?
    {s = Sort.FORMULA;}
    ids = simple_ident_comma_list
  | (    TERM
         { mods = new SchemaVariableModifierSet.TermSV (); }
         ( schema_modifiers[mods] ) ?
      | ( (VARIABLES | VARIABLE)
         { makeVariableSV = true; }
         { mods = new SchemaVariableModifierSet.VariableSV (); }
         ( schema_modifiers[mods] ) ?)
      | (SKOLEMTERM
         { makeSkolemTermSV = true; }
         { mods = new SchemaVariableModifierSet.SkolemTermSV (); }
         ( schema_modifiers[mods] ) ?)
    )
    s = any_sortId_check[true]
    ids = simple_ident_comma_list
  ) SEMI
   {
     Iterator<String> it = ids.iterator();
     while(it.hasNext())
       schema_var_decl(it.next(),
                       s,
                       makeVariableSV,
                       makeSkolemTermSV,
                       makeTermLabelSV,
		       mods);
   }
 )
         */
        return super.visitOne_schema_var_decl(ctx);
    }

    @Override
    public Object visitSchema_modifiers(KeYParser.Schema_modifiersContext ctx) {
        var ids = visitSimple_ident_comma_list(ctx.simple_ident_comma_list());
        for (String id : ids) {
            if (!mods.addModifier(id))
                semanticError(id +
                        ": Illegal or unknown modifier in declaration of schema variable");
        }
        return null;
    }

    @Override
    public Object visitOne_schema_modal_op_decl(KeYParser.One_schema_modal_op_declContext ctx) {
        //TODO
        /*
              (LPAREN sort = any_sortId_check[true] {
           if (sort != Sort.FORMULA) {
               semanticError("Modal operator SV must be a FORMULA, not " + sort);
           }
         } RPAREN)?
        LBRACE ids = simple_ident_comma_list RBRACE id = simple_ident
	{   if (skip_schemavariables) {
	       return;
	    }
            Iterator<String> it1 = ids.iterator();
            while(it1.hasNext()) {
  	      modalities = opSVHelper(it1.next(), modalities);
  	    }
            SchemaVariable osv = schemaVariables().lookup(new Name(id));
            if(osv != null)
              semanticError("Schema variable "+id+" already defined.");

            osv = SchemaVariableFactory.createModalOperatorSV(new Name(id),
                        sort, modalities);

            if (inSchemaMode()) {
                schemaVariables().add(osv);
                //functions().add(osv);
            }
        }
         */
        return super.visitOne_schema_modal_op_decl(ctx);
    }

    @Override
    public Object visitPred_decl(KeYParser.Pred_declContext ctx) {
        //TODO
        /*
           pred_name = funcpred_name

        (
	    whereToBind = where_to_bind
	)?


        argSorts = arg_sorts[!skip_predicates]
        {
            if (!skip_predicates) {

                if(whereToBind != null
	 	   && whereToBind.length != argSorts.length) {
                    semanticError("Where-to-bind list must have same length "
                                  + "as argument list");
                }

                Function p = null;

            	int separatorIndex = pred_name.indexOf("::");
	        if (separatorIndex > 0) {
	            String sortName = pred_name.substring(0, separatorIndex);
	            String baseName = pred_name.substring(separatorIndex + 2);
		    Sort genSort = lookupSort(sortName);

		    if(genSort instanceof GenericSort) {
		    	p = SortDependingFunction.createFirstInstance(
		    	    		(GenericSort)genSort,
		    	    		new Name(baseName),
		    	    		Sort.FORMULA,
		    	    		argSorts,
		    	    		false);
		    }
	        }

                if(p == null) {
                    p = new Function(new Name(pred_name),
                    		     Sort.FORMULA,
                    		     argSorts,
                    		     whereToBind,
                    		     false);
                }
		if (lookup(p.name()) != null) {
		    if(!isProblemParser()) {
		        throw new AmbigiousDeclException(p.name().toString(),
		                                         getSourceName(),
		                                         getLine(),
		                                         getColumn());

		    }
		}else{
                  addFunction(p);
                }
            }
        }
        SEMI
         */
        return super.visitPred_decl(ctx);
    }

    @Override
    public Object visitPred_decls(KeYParser.Pred_declsContext ctx) {
        return super.visitPred_decls(ctx);
    }

    @Override
    public Integer visitLocation_ident(KeYParser.Location_identContext ctx) {
        var id = visit(ctx.simple_ident());
        if ("Location".equals(id)) {
            return LOCATION_MODIFIER;
        } else if (!"Location".equals(id)) {
            semanticError(
                    id + ": Attribute of a Non Rigid Function can only be 'Location'");
        }
        return NORMAL_NONRIGID;
    }

    @Override
    public Object visitFunc_decl(KeYParser.Func_declContext ctx) {
        //TODO
        /*
        func_decl
@init{
    boolean unique = false;
}
    :
        (
            UNIQUE {unique=true;}
        )?

        retSort = any_sortId_check[!skip_functions]

        func_name = funcpred_name

	(
	    whereToBind = where_to_bind
	)?

        argSorts = arg_sorts[!skip_functions]

        {
            if (!skip_functions) {

	 	if(whereToBind != null
	 	   && whereToBind.length != argSorts.length) {
                    semanticError("Where-to-bind list must have same length "
                                  + "as argument list");
                }

                Function f = null;

	        int separatorIndex = func_name.indexOf("::");
	        if (separatorIndex > 0) {
	            String sortName = func_name.substring(0, separatorIndex);
	            String baseName = func_name.substring(separatorIndex + 2);
		    Sort genSort = lookupSort(sortName);

		    if(genSort instanceof GenericSort) {
		    	f = SortDependingFunction.createFirstInstance(
		    	    		(GenericSort)genSort,
		    	    		new Name(baseName),
		    	    		retSort,
		    	    		argSorts,
		    	    		unique);
		    }
	        }

	        if(f == null) {
	            f = new Function(new Name(func_name),
	                             retSort,
	                             argSorts,
	                             whereToBind,
	                             unique);
	        }
		if (lookup(f.name()) != null) {
		    if(!isProblemParser()) {
		      throw new AmbigiousDeclException(f.name().toString(),
		                                     getSourceName(),
		                                     getLine(),
		                                     getColumn());
		    }
		}else{
	    	    addFunction(f);
	        }
            }
        }
        SEMI
    ;
         */
        return super.visitFunc_decl(ctx);
    }

    @Override
    public Object visitFunc_decls(KeYParser.Func_declsContext ctx) {
        return super.visitFunc_decls(ctx);
    }

    @Override
    public List<Sort> visitArg_sorts_or_formula(KeYParser.Arg_sorts_or_formulaContext ctx) {
        return mapOf(ctx.arg_sorts_or_formula_helper());
    }

    @Override
    public Sort visitArg_sorts_or_formula_helper(KeYParser.Arg_sorts_or_formula_helperContext ctx) {
        if (ctx.FORMULA() != null)
            return Sort.FORMULA;
        else
            return (Sort) visit(ctx.sortId_check());
    }

    @Override
    public Object visitTransform_decl(KeYParser.Transform_declContext ctx) {
        var retSort = (Sort) (ctx.FORMULA() != null ? Sort.FORMULA : visit(ctx.any_sortId_check()));
        var trans_name = (String) visit(ctx.funcpred_name());
        var argSorts = (List<Sort>) visit(ctx.arg_sorts_or_formula());
        if (!skip_transformers) {
            Transformer t =
                    new Transformer(new Name(trans_name),
                            retSort,
                            new ImmutableArray<>(argSorts));
            if (lookup(t.name()) != null) {
                if (!isProblemParser()) {
                    throwEx(new AmbigiousDeclException(t.name().toString(),
                            getSourceName(),
                            getLine(),
                            getColumn()));
                }
            } else {
                addFunction(t);
            }
        }
        return null;
    }

    @Override
    public Object visitTransform_decls(KeYParser.Transform_declsContext ctx) {
        return super.visitTransform_decls(ctx);
    }

    @Override
    public KeYJavaType visitArrayopid(KeYParser.ArrayopidContext ctx) {
        return (KeYJavaType) visit(ctx.keyjavatype());
    }

    @Override
    public List<Sort> visitArg_sorts(KeYParser.Arg_sortsContext ctx) {
        return mapOf(ctx.sortId_check());
    }

    @Override
    public List<Boolean> visitWhere_to_bind(KeYParser.Where_to_bindContext ctx) {
        List<Boolean> list = new ArrayList<>(ctx.children.size());
        ctx.b.forEach(it -> list.add(it.getText().equalsIgnoreCase("true")));
        return list;
    }

    @Override
    public Object visitRuleset_decls(KeYParser.Ruleset_declsContext ctx) {
        if (!skip_rulesets) {
            for (String id : this.<String>mapOf(ctx.simple_ident())) {
                RuleSet h = new RuleSet(new Name(id));
                if (ruleSets().lookup(new Name(id)) == null) {
                    ruleSets().add(h);
                }
            }
        }
        return super.visitRuleset_decls(ctx);
    }

    @Override
    public Sort visitSortId(KeYParser.SortIdContext ctx) {
        return (Sort) ctx.sortId_check().accept(this);
    }

    @Override
    public Sort visitSortId_check(KeYParser.SortId_checkContext ctx) {
        var p = visit(ctx.sortId_check_help());
        return (Sort) visit(ctx.array_decls());
    }

    @Override
    public Sort visitAny_sortId_check(KeYParser.Any_sortId_checkContext ctx) {
        var p = visit(ctx.any_sortId_check_help());
        return (Sort) visit(ctx.array_decls());
    }

    @Override
    public Pair<Sort, Type> visitSortId_check_help(KeYParser.SortId_check_helpContext ctx) {
        Pair<Sort, Type> result = (Pair<Sort, Type>) visit(ctx.any_sortId_check_help());
        // don't allow generic sorts or collection sorts of
        // generic sorts at this point
        Sort s = result.first;
        while (s instanceof ArraySort) {
            s = ((ArraySort) s).elementSort();
        }

        if (s instanceof GenericSort) {
            throwEx(new GenericSortException("sort",
                    "Non-generic sort expected", s,
                    getSourceName(), getLine(), getColumn()));
        }

        return result;
    }

    @Override
    public Pair<Sort, Type> visitAny_sortId_check_help(KeYParser.Any_sortId_check_helpContext ctx) {
        var name = (String) visit(ctx.simple_sort_name());
        //Special handling for byte, char, short, long:
        //these are *not* sorts, but they are nevertheless valid
        //prefixes for array sorts such as byte[], char[][][].
        //Thus, we consider them aliases for the "int" sort, and remember
        //the corresponding Java type for the case that an array sort
        //is being declared.
        Type t = null;
        if (name.equals(PrimitiveType.JAVA_BYTE.getName())) {
            t = PrimitiveType.JAVA_BYTE;
            name = PrimitiveType.JAVA_INT.getName();
        } else if (name.equals(PrimitiveType.JAVA_CHAR.getName())) {
            t = PrimitiveType.JAVA_CHAR;
            name = PrimitiveType.JAVA_INT.getName();
        } else if (name.equals(PrimitiveType.JAVA_SHORT.getName())) {
            t = PrimitiveType.JAVA_SHORT;
            name = PrimitiveType.JAVA_INT.getName();
        } else if (name.equals(PrimitiveType.JAVA_INT.getName())) {
            t = PrimitiveType.JAVA_INT;
            name = PrimitiveType.JAVA_INT.getName();
        } else if (name.equals(PrimitiveType.JAVA_LONG.getName())) {
            t = PrimitiveType.JAVA_LONG;
            name = PrimitiveType.JAVA_INT.getName();
        } else if (name.equals(PrimitiveType.JAVA_BIGINT.getName())) {
            t = PrimitiveType.JAVA_BIGINT;
            name = PrimitiveType.JAVA_BIGINT.getName();
        }

        Sort s = null;
        if (checkSort) {
            s = lookupSort(name);
            if (s == null) {
                throwEx(new NotDeclException(input, "sort", name));
            }
        }
        return new Pair<Sort, Type>(s, t);
    }

    public Sort visitArray_decls(Pair<Sort, Type> p, KeYParser.Array_declsContext ctx) {
        Sort s = null;
        int n = ctx.EMPTYBRACKETS().size();

        if (!checkSort)
            return s;
        if (n != 0) {
            final JavaInfo ji = getJavaInfo();
            s = ArraySort.getArraySortForDim(p.first,
                    p.second,
                    n,
                    ji.objectSort(),
                    ji.cloneableSort(),
                    ji.serializableSort());

            Sort last = s;
            do {
                final ArraySort as = (ArraySort) last;
                sorts().add(as);
                last = as.elementSort();
            } while (last instanceof ArraySort && sorts().lookup(last.name()) == null);
        } else {
            s = p.first;
        }
        return s;
    }

    @Override
    public IdDeclaration visitId_declaration(KeYParser.Id_declarationContext ctx) {
        var id = (String) visit(ctx.IDENT());
        var s = (Sort) (ctx.sortId_check() != null ? visit(ctx.sortId_check()) : null);
        return new IdDeclaration(id, s);
    }

    @Override
    public String visitFuncpred_name(KeYParser.Funcpred_nameContext ctx) {
        if (ctx.DOUBLECOLON() != null) {
            return visit(ctx.sort_name()) + "::" + visit(ctx.name);
        }
        return (String) visit(ctx.simple_ident());
    }

    @Override
    public String visitSimple_sort_name(KeYParser.Simple_sort_nameContext ctx) {
        return (String) visit(ctx.simple_ident_dots());
    }

    @Override
    public String visitSort_name(KeYParser.Sort_nameContext ctx) {
        String name = (String) visit(ctx.simple_sort_name());
        for (int i = 0; i < ctx.EMPTYBRACKETS().size(); i++) {
            name += "[]";
        }
        return name;
    }

    @Override
    public Term visitFormula(KeYParser.FormulaContext ctx) {
        Term a = (Term) visit(ctx.term());
        if (a != null && a.sort() != Sort.FORMULA) {
            semanticError("Just Parsed a Term where a Formula was expected.");
        }
        return a;
    }

    @Override
    public Term visitTerm(KeYParser.TermContext ctx) {
        var terms = this.<Term>mapOf(ctx.elementary_update_term());
        var result = getTermFactory().createTerm(UpdateJunctor.PARALLEL_UPDATE, terms);
        return result;
    }

    @Override
    public Term visitTermEOF(KeYParser.TermEOFContext ctx) {
        return (Term) visit(ctx.term());
    }

    @Override
    public Term visitElementary_update_term(KeYParser.Elementary_update_termContext ctx) {
        List<Term> terms = mapOf(ctx.equivalence_term());
        return getServices().getTermBuilder().elementary(terms);
    }

    @Override
    public Term visitEquivalence_term(KeYParser.Equivalence_termContext ctx) {
        List<Term> terms = mapOf(ctx.implication_term());
        return getTermFactory().createTerm(Equality.EQV, terms);
    }

    @Override
    public Term visitImplication_term(KeYParser.Implication_termContext ctx) {
        var a = (Term) visit(ctx.a);
        var a1 = (Term) visit(ctx.a1);
        return getTermFactory().createTerm(Junctor.IMP, a, a1);
    }

    @Override
    public Term visitDisjunction_term(KeYParser.Disjunction_termContext ctx) {
        List<Term> terms = mapOf(ctx.conjunction_term());
        return getTermFactory().createTerm(Junctor.OR, terms);
    }

    @Override
    public Term visitConjunction_term(KeYParser.Conjunction_termContext ctx) {
        List<Term> terms = mapOf(ctx.term60());
        return getTermFactory().createTerm(Junctor.AND, terms);
    }

    @Override
    public Term visitTerm60(KeYParser.Term60Context ctx) {
        return (Term) super.visitTerm60(ctx);
    }

    @Override
    public Term visitUnary_formula(KeYParser.Unary_formulaContext ctx) {
        if (ctx.NOT() != null) {
            return getTermFactory().createTerm(Junctor.NOT, new Term[]{
                    (Term) visit(ctx.term60())});
        }
        return (Term) super.visitUnary_formula(ctx);
    }

    @Override
    public Object visitEquality_term(KeYParser.Equality_termContext ctx) {
        Term a = (Term) visit(ctx.a);
        if (ctx.EQUALS() == null && null == ctx.NOT_EQUALS()) {
            return a;
        }

        boolean negated = ctx.NOT_EQUALS() != null;
        Term b = (Term) visit(ctx.a1);
        if (a.sort() == Sort.FORMULA || b.sort() == Sort.FORMULA) {
            String errorMessage =
                    "The term equality \'=\'/\'!=\' is not " +
                            "allowed between formulas.\n Please use \'" + Equality.EQV +
                            "\' in combination with \'" + Junctor.NOT + "\' instead.";
            if (a.op() == Junctor.TRUE || a.op() == Junctor.FALSE ||
                    b.op() == Junctor.TRUE || b.op() == Junctor.FALSE) {
                errorMessage +=
                        " It seems as if you have mixed up the boolean " +
                                "constants \'TRUE\'/\'FALSE\' " +
                                "with the formulas \'true\'/\'false\'.";
            }
            semanticError(errorMessage);
        }
        a = getTermFactory().createTerm(Equality.EQUALS, a, b);
        if (negated) {
            a = getTermFactory().createTerm(Junctor.NOT, a);
        }
        return a;
    }

    @Override
    public Object visitRelation_op(KeYParser.Relation_opContext ctx) {
        String op_name = "";
        if (ctx.LESS() != null)
            op_name = "lt";
        if (ctx.LESSEQUAL() != null)
            op_name = "leq";
        if (ctx.GREATER() != null)
            op_name = "gt";
        if (ctx.GREATEREQUAL() != null)
            op_name = "geq";
        var op = (Function) functions().lookup(new Name(op_name));
        if (op == null) {
            semanticError("Function symbol '" + op_name + "' not found.");
        }
        return op;
    }

    @Override
    public Object visitWeak_arith_op(KeYParser.Weak_arith_opContext ctx) {
        String op_name = "";
        if (ctx.PLUS() != null) {
            op_name = "add";
        }
        if (ctx.MINUS() != null) {
            op_name = "sub";
        }
        var op = (Function) functions().lookup(new Name(op_name));
        if (op == null) {
            semanticError("Function symbol '" + op_name + "' not found.");
        }
        return op;
    }

    @Override
    public Object visitStrong_arith_op(KeYParser.Strong_arith_opContext ctx) {
        String op_name = "";
        if (ctx.STAR() != null) {
            op_name = "mul";
        }
        if (ctx.SLASH() != null) {
            op_name = "div";
        }
        if (ctx.PERCENT() != null) {
            op_name = "mod";
        }
        var op = (Function) functions().lookup(new Name(op_name));
        if (op == null) {
            semanticError("Function symbol '" + op_name + "' not found.");
        }
        return op;
    }

    @Override
    public Object visitLogicTermReEntry(KeYParser.LogicTermReEntryContext ctx) {
        Term a = (Term) visit(ctx.a);
        if (ctx.op == null) return a;
        Function op = (Function) visit(ctx.op);
        Term a1 = (Term) visit(ctx.a1);
        return getTermFactory().createTerm(op, a, a1);
    }

    @Override
    public Object visitWeak_arith_op_term(KeYParser.Weak_arith_op_termContext ctx) {
        Term a = (Term) visit(ctx.a);
        if (ctx.op == null) return a;
        Function op = (Function) visit(ctx.op);
        Term a1 = (Term) visit(ctx.a1);
        return getTermFactory().createTerm(op, a, a1);
    }

    @Override
    public Object visitStrong_arith_op_term(KeYParser.Strong_arith_op_termContext ctx) {
        Term a = (Term) visit(ctx.a);
        if (ctx.op == null) return a;
        Function op = (Function) visit(ctx.op);
        Term a1 = (Term) visit(ctx.a1);
        return getTermFactory().createTerm(op, a, a1);
    }

    @Override
    public Object visitTerm110(KeYParser.Term110Context ctx) {
        if (ctx.braces_term() != null)
            return visit(ctx.braces_term());
        else
            return visit(ctx.accessterm());
    }

    @Override
    public Object visitStaticAttributeOrQueryReference(KeYParser.StaticAttributeOrQueryReferenceContext ctx) {
        return super.visitStaticAttributeOrQueryReference(ctx);
    }

    @Override
    public Object visitStatic_attribute_suffix(KeYParser.Static_attribute_suffixContext ctx) {
        return super.visitStatic_attribute_suffix(ctx);
    }

    @Override
    public Object visitAttribute_or_query_suffix(KeYParser.Attribute_or_query_suffixContext ctx) {
        return super.visitAttribute_or_query_suffix(ctx);
    }

    @Override
    public Object visitAttrid(KeYParser.AttridContext ctx) {
        return super.visitAttrid(ctx);
    }

    @Override
    public Object visitQuery_suffix(KeYParser.Query_suffixContext ctx) {
        return super.visitQuery_suffix(ctx);
    }

    @Override
    public Object visitAccessterm(KeYParser.AccesstermContext ctx) {
        return super.visitAccessterm(ctx);
    }

    @Override
    public Object visitHeap_selection_suffix(KeYParser.Heap_selection_suffixContext ctx) {
        return super.visitHeap_selection_suffix(ctx);
    }

    @Override
    public Object visitAccessterm_bracket_suffix(KeYParser.Accessterm_bracket_suffixContext ctx) {
        return super.visitAccessterm_bracket_suffix(ctx);
    }

    @Override
    public Object visitSeq_get_suffix(KeYParser.Seq_get_suffixContext ctx) {
        return super.visitSeq_get_suffix(ctx);
    }

    @Override
    public Object visitStatic_query(KeYParser.Static_queryContext ctx) {
        return super.visitStatic_query(ctx);
    }

    @Override
    public Object visitHeap_update_suffix(KeYParser.Heap_update_suffixContext ctx) {
        return super.visitHeap_update_suffix(ctx);
    }

    @Override
    public Object visitArray_access_suffix(KeYParser.Array_access_suffixContext ctx) {
        return super.visitArray_access_suffix(ctx);
    }

    @Override
    public Object visitAtom(KeYParser.AtomContext ctx) {
        return super.visitAtom(ctx);
    }

    @Override
    public Object visitLabel(KeYParser.LabelContext ctx) {
        return super.visitLabel(ctx);
    }

    @Override
    public Object visitSingle_label(KeYParser.Single_labelContext ctx) {
        return super.visitSingle_label(ctx);
    }

    @Override
    public Object visitAbbreviation(KeYParser.AbbreviationContext ctx) {
        return super.visitAbbreviation(ctx);
    }

    @Override
    public Term visitIfThenElseTerm(KeYParser.IfThenElseTermContext ctx) {
        var condF = (Term) ctx.condF.accept(this);
        if (condF.sort() != Sort.FORMULA) {
            semanticError
                    ("Condition of an \\if-then-else term has to be a formula.");
        }
        var thenT = (Term) ctx.thenT.accept(this);
        var elseT = (Term) ctx.elseT.accept(this);
        return getTermFactory().createTerm(IfThenElse.IF_THEN_ELSE, new Term[]{condF, thenT, elseT});
    }

    @Override
    public Object visitIfExThenElseTerm(KeYParser.IfExThenElseTermContext ctx) {
        Namespace<QuantifiableVariable> orig = variables();
        var exVars = visit(ctx.bound_variables());
        var condF = (Term) visit(ctx.condF);
        if (condF.sort() != Sort.FORMULA) {
            semanticError
                    ("Condition of an \\ifEx-then-else term has to be a formula.");
        }

        var thenT = (Term) visit(ctx.thenT);
        var elseT = (Term) visit(ctx.elseT);
        ImmutableArray<QuantifiableVariable> exVarsArray
                = new ImmutableArray<QuantifiableVariable>(
                exVars.toArray(new QuantifiableVariable[exVars.size()]));
        var result = getTermFactory().createTerm(IfExThenElse.IF_EX_THEN_ELSE,
                new Term[]{condF, thenT, elseT},
                exVarsArray,
                null);
        if (!isGlobalDeclTermParser()) {
            unbindVars(orig);
        }
        return result;
    }

    @Override
    public Term visitArgument(KeYParser.ArgumentContext ctx) {
        return (Term) super.visitArgument(ctx);
    }

    @Override
    public Term visitQuantifierterm(KeYParser.QuantifiertermContext ctx) {
        Operator op = null;
        Namespace<QuantifiableVariable> orig = variables();
        if (ctx.FORALL() != null)
            op = Quantifier.ALL;
        if (ctx.EXISTS() != null)
            op = Quantifier.EX;
        var vs = visit(ctx.bound_variables());
        var a1 = (Term) visit(ctx.term60());
        var a = getTermFactory().createTerm((Quantifier) op,
                new ImmutableArray<Term>(a1),
                new ImmutableArray<QuantifiableVariable>(vs.toArray(new QuantifiableVariable[vs.size()])),
                null);
        if (!isGlobalDeclTermParser())
            unbindVars(orig);
        return a;
    }

    @Override
    public Term visitBraces_term(KeYParser.Braces_termContext ctx) {
        return (Term) super.visitBraces_term(ctx);
    }

    @Override
    public Term visitLocset_term(KeYParser.Locset_termContext ctx) {
        List<Term> terms = mapOf(ctx.location_term());
        return getServices().getTermBuilder().union(terms);
    }

    @Override
    public Object visitLocation_term(KeYParser.Location_termContext ctx) {
        var obj = (Term) visit(ctx.obj);
        var field = (Term) visit(ctx.field);
        return getServices().getTermBuilder().singleton(obj, field);
    }

    @Override
    public Term visitSubstitutionterm(KeYParser.SubstitutiontermContext ctx) {
        return super.visitSubstitutionterm(ctx);
    }

    @Override
    public Term visitUpdateterm(KeYParser.UpdatetermContext ctx) {
        return super.visitUpdateterm(ctx);
    }

    @Override
    public Term visitBound_variables(KeYParser.Bound_variablesContext ctx) {
        return super.visitBound_variables(ctx);
    }

    @Override
    public Object visitOne_bound_variable(KeYParser.One_bound_variableContext ctx) {
        return super.visitOne_bound_variable(ctx);
    }

    @Override
    public Object visitOne_schema_bound_variable(KeYParser.One_schema_bound_variableContext ctx) {
        return super.visitOne_schema_bound_variable(ctx);
    }

    @Override
    public Object visitOne_logic_bound_variable(KeYParser.One_logic_bound_variableContext ctx) {
        return super.visitOne_logic_bound_variable(ctx);
    }

    @Override
    public Object visitOne_logic_bound_variable_nosort(KeYParser.One_logic_bound_variable_nosortContext ctx) {
        return super.visitOne_logic_bound_variable_nosort(ctx);
    }

    @Override
    public Object visitModality_dl_term(KeYParser.Modality_dl_termContext ctx) {
        return super.visitModality_dl_term(ctx);
    }

    @Override
    public Object visitArgument_list(KeYParser.Argument_listContext ctx) {
        return super.visitArgument_list(ctx);
    }

    @Override
    public Object visitFuncpredvarterm(KeYParser.FuncpredvartermContext ctx) {
        return super.visitFuncpredvarterm(ctx);
    }

    @Override
    public Object visitSpecialTerm(KeYParser.SpecialTermContext ctx) {
        return super.visitSpecialTerm(ctx);
    }

    @Override
    public Object visitArith_op(KeYParser.Arith_opContext ctx) {
        return super.visitArith_op(ctx);
    }

    @Override
    public Object visitVarId(KeYParser.VarIdContext ctx) {
        return super.visitVarId(ctx);
    }

    @Override
    public Object visitVarIds(KeYParser.VarIdsContext ctx) {
        return super.visitVarIds(ctx);
    }

    @Override
    public Object visitTriggers(KeYParser.TriggersContext ctx) {
        return super.visitTriggers(ctx);
    }

    @Override
    public Object visitTaclet(KeYParser.TacletContext ctx) {
        return super.visitTaclet(ctx);
    }

    @Override
    public Object visitTacletgen(KeYParser.TacletgenContext ctx) {
        return super.visitTacletgen(ctx);
    }

    @Override
    public Object visitModifiers(KeYParser.ModifiersContext ctx) {
        return super.visitModifiers(ctx);
    }

    @Override
    public Object visitSeq(KeYParser.SeqContext ctx) {
        return super.visitSeq(ctx);
    }

    @Override
    public Object visitSeqEOF(KeYParser.SeqEOFContext ctx) {
        return super.visitSeqEOF(ctx);
    }

    @Override
    public Object visitTermorseq(KeYParser.TermorseqContext ctx) {
        return super.visitTermorseq(ctx);
    }

    @Override
    public Object visitSemisequent(KeYParser.SemisequentContext ctx) {
        return super.visitSemisequent(ctx);
    }

    @Override
    public Object visitVarexplist(KeYParser.VarexplistContext ctx) {
        return super.visitVarexplist(ctx);
    }

    @Override
    public Object visitVarexp(KeYParser.VarexpContext ctx) {
        return super.visitVarexp(ctx);
    }

    @Override
    public Object visitVarcond_sameObserver(KeYParser.Varcond_sameObserverContext ctx) {
        return super.visitVarcond_sameObserver(ctx);
    }

    @Override
    public Object visitVarcond_applyUpdateOnRigid(KeYParser.Varcond_applyUpdateOnRigidContext ctx) {
        return super.visitVarcond_applyUpdateOnRigid(ctx);
    }

    @Override
    public Object visitVarcond_dropEffectlessElementaries(KeYParser.Varcond_dropEffectlessElementariesContext ctx) {
        return super.visitVarcond_dropEffectlessElementaries(ctx);
    }

    @Override
    public Object visitVarcond_dropEffectlessStores(KeYParser.Varcond_dropEffectlessStoresContext ctx) {
        return super.visitVarcond_dropEffectlessStores(ctx);
    }

    @Override
    public Object visitVarcond_differentFields(KeYParser.Varcond_differentFieldsContext ctx) {
        return super.visitVarcond_differentFields(ctx);
    }

    @Override
    public Object visitVarcond_simplifyIfThenElseUpdate(KeYParser.Varcond_simplifyIfThenElseUpdateContext ctx) {
        return super.visitVarcond_simplifyIfThenElseUpdate(ctx);
    }

    @Override
    public Object visitType_resolver(KeYParser.Type_resolverContext ctx) {
        return super.visitType_resolver(ctx);
    }

    @Override
    public Object visitVarcond_new(KeYParser.Varcond_newContext ctx) {
        return super.visitVarcond_new(ctx);
    }

    @Override
    public Object visitVarcond_newlabel(KeYParser.Varcond_newlabelContext ctx) {
        return super.visitVarcond_newlabel(ctx);
    }

    @Override
    public Object visitVarcond_typecheck(KeYParser.Varcond_typecheckContext ctx) {
        return super.visitVarcond_typecheck(ctx);
    }

    @Override
    public Object visitVarcond_free(KeYParser.Varcond_freeContext ctx) {
        return super.visitVarcond_free(ctx);
    }

    @Override
    public Object visitVarcond_hassort(KeYParser.Varcond_hassortContext ctx) {
        return super.visitVarcond_hassort(ctx);
    }

    @Override
    public Object visitVarcond_fieldtype(KeYParser.Varcond_fieldtypeContext ctx) {
        return super.visitVarcond_fieldtype(ctx);
    }

    @Override
    public Object visitVarcond_containsAssignment(KeYParser.Varcond_containsAssignmentContext ctx) {
        return super.visitVarcond_containsAssignment(ctx);
    }

    @Override
    public Object visitVarcond_enumtype(KeYParser.Varcond_enumtypeContext ctx) {
        return super.visitVarcond_enumtype(ctx);
    }

    @Override
    public Object visitVarcond_reference(KeYParser.Varcond_referenceContext ctx) {
        return super.visitVarcond_reference(ctx);
    }

    @Override
    public Object visitVarcond_thisreference(KeYParser.Varcond_thisreferenceContext ctx) {
        return super.visitVarcond_thisreference(ctx);
    }

    @Override
    public Object visitVarcond_staticmethod(KeYParser.Varcond_staticmethodContext ctx) {
        return super.visitVarcond_staticmethod(ctx);
    }

    @Override
    public Object visitVarcond_mayexpandmethod(KeYParser.Varcond_mayexpandmethodContext ctx) {
        return super.visitVarcond_mayexpandmethod(ctx);
    }

    @Override
    public Object visitVarcond_referencearray(KeYParser.Varcond_referencearrayContext ctx) {
        return super.visitVarcond_referencearray(ctx);
    }

    @Override
    public Object visitVarcond_array(KeYParser.Varcond_arrayContext ctx) {
        return super.visitVarcond_array(ctx);
    }

    @Override
    public Object visitVarcond_array_length(KeYParser.Varcond_array_lengthContext ctx) {
        return super.visitVarcond_array_length(ctx);
    }

    @Override
    public Object visitVarcond_abstractOrInterface(KeYParser.Varcond_abstractOrInterfaceContext ctx) {
        return super.visitVarcond_abstractOrInterface(ctx);
    }

    @Override
    public Object visitVarcond_enum_const(KeYParser.Varcond_enum_constContext ctx) {
        return super.visitVarcond_enum_const(ctx);
    }

    @Override
    public Object visitVarcond_final(KeYParser.Varcond_finalContext ctx) {
        return super.visitVarcond_final(ctx);
    }

    @Override
    public Object visitVarcond_static(KeYParser.Varcond_staticContext ctx) {
        return super.visitVarcond_static(ctx);
    }

    @Override
    public Object visitVarcond_localvariable(KeYParser.Varcond_localvariableContext ctx) {
        return super.visitVarcond_localvariable(ctx);
    }

    @Override
    public Object visitVarcond_observer(KeYParser.Varcond_observerContext ctx) {
        return super.visitVarcond_observer(ctx);
    }

    @Override
    public Object visitVarcond_different(KeYParser.Varcond_differentContext ctx) {
        return super.visitVarcond_different(ctx);
    }

    @Override
    public Object visitVarcond_metadisjoint(KeYParser.Varcond_metadisjointContext ctx) {
        return super.visitVarcond_metadisjoint(ctx);
    }

    @Override
    public Object visitVarcond_equalUnique(KeYParser.Varcond_equalUniqueContext ctx) {
        return super.visitVarcond_equalUnique(ctx);
    }

    @Override
    public Object visitVarcond_freeLabelIn(KeYParser.Varcond_freeLabelInContext ctx) {
        return super.visitVarcond_freeLabelIn(ctx);
    }

    @Override
    public Object visitVarcond_constant(KeYParser.Varcond_constantContext ctx) {
        return super.visitVarcond_constant(ctx);
    }

    @Override
    public Object visitVarcond_label(KeYParser.Varcond_labelContext ctx) {
        return super.visitVarcond_label(ctx);
    }

    @Override
    public Object visitVarcond_static_field(KeYParser.Varcond_static_fieldContext ctx) {
        return super.visitVarcond_static_field(ctx);
    }

    @Override
    public Object visitVarcond_subFormulas(KeYParser.Varcond_subFormulasContext ctx) {
        return super.visitVarcond_subFormulas(ctx);
    }

    @Override
    public Object visitGoalspecs(KeYParser.GoalspecsContext ctx) {
        return super.visitGoalspecs(ctx);
    }

    @Override
    public Object visitGoalspecwithoption(KeYParser.GoalspecwithoptionContext ctx) {
        return super.visitGoalspecwithoption(ctx);
    }

    @Override
    public Object visitOption(KeYParser.OptionContext ctx) {
        return super.visitOption(ctx);
    }

    @Override
    public Object visitOption_list(KeYParser.Option_listContext ctx) {
        return super.visitOption_list(ctx);
    }

    @Override
    public Object visitGoalspec(KeYParser.GoalspecContext ctx) {
        return super.visitGoalspec(ctx);
    }

    @Override
    public Object visitReplacewith(KeYParser.ReplacewithContext ctx) {
        return super.visitReplacewith(ctx);
    }

    @Override
    public Object visitAdd(KeYParser.AddContext ctx) {
        return super.visitAdd(ctx);
    }

    @Override
    public Object visitAddrules(KeYParser.AddrulesContext ctx) {
        return super.visitAddrules(ctx);
    }

    @Override
    public Object visitAddprogvar(KeYParser.AddprogvarContext ctx) {
        return super.visitAddprogvar(ctx);
    }

    @Override
    public Object visitTacletlist(KeYParser.TacletlistContext ctx) {
        lor = ImmutableSLList.<Taclet>nil();
        head = taclet[DefaultImmutableSet.<Choice>nil(), false]
        ( /*empty*/ | COMMA lor = tacletlist){
            lor = lor.prepend(head);
        }
    }

    @Override
    public Object visitPvset(KeYParser.PvsetContext ctx) {
        pvs = DefaultImmutableSet.<SchemaVariable>nil();
        pv = varId
                ( /*empty*/ | COMMA pvs = pvset)
        pvs = pvs.add
                ((SchemaVariable) pv);
    }

    @Override
    public List<RuleSet> visitRulesets(KeYParser.RulesetsContext ctx) {
        return mapOf(ctx.ruleset());
    }

    @Override
    public Object visitRuleset(KeYParser.RulesetContext ctx) {
        String id = (String) ctx.IDENT().accept(this);
        RuleSet h = (RuleSet) ruleSets().lookup(new Name(id));
        if (h == null) {
            throwEx(new NotDeclException(input, "ruleset", id));
        }
        return h;
    }

    @Override
    public Object visitMetaId(KeYParser.MetaIdContext ctx) {
        var id = visitSimple_ident(ctx.simple_ident());
        TermTransformer v = AbstractTermTransformer.name2metaop(id);
        if (v == null)
            semanticError("Unknown metaoperator: " + id);
        return v;
    }

    @Override
    public Object visitMetaTerm(KeYParser.MetaTermContext ctx) {
        (vf = metaId
                (LPAREN
                        t = term
        {
            al.add(t);
        }
        (COMMA
        t = term
        {
            al.add(t);
        }
        )*RPAREN)?
        {
            result = getTermFactory().createTerm(vf, (Term[]) al.toArray(AN_ARRAY_OF_TERMS));
        }
        )}

    @Override
    public Object visitContracts(KeYParser.ContractsContext ctx) {
        return super.visitContracts(ctx);
    }

    @Override
    public Object visitInvariants(KeYParser.InvariantsContext ctx) {
        Namespace<QuantifiableVariable> orig = variables();
        selfVar = (ParsableVariable) ctx.one_logic_bound_variable().accept(this);
        ctx.one_invariant().forEach(it -> it.accept(this));
        unbindVars(orig);
        return null;
    }

    @Override
    public Object visitOne_contract(KeYParser.One_contractContext ctx) {
        String contractName = visitSimple_ident(ctx.contractName);
        //for program variable declarations
        namespaces().setProgramVariables(new Namespace(programVariables()));
        var fma = visitFormula(ctx.formula());
        var modifiesClause = visitTerm(ctx.modifiesClause);
        DLSpecFactory dsf = new DLSpecFactory(getServices());
        try {
            contracts = contracts.prepend(dsf.createDLOperationContract(contractName,
                    fma,
                    modifiesClause));
        } catch (ProofInputException e) {
            semanticError(e.getMessage());
        }
        //dump local program variable declarations
        namespaces().setProgramVariables(programVariables().parent());
        return null;
    }


    @Override
    public Object visitOne_invariant(KeYParser.One_invariantContext ctx) {
        String invName = visitSimple_ident(ctx.simple_ident());
        var fma = visitFormula(ctx.formula());
        var displayName = ctx.displayName != null ? ctx.displayName.getText() : null;
        DLSpecFactory dsf = new DLSpecFactory(getServices());
        try {
            invs = invs.add(dsf.createDLClassInvariant(invName,
                    displayName,
                    selfVar,
                    fma));
        } catch (ProofInputException e) {
            semanticError(e.getMessage());
        }
        return null;
    }

    @Override
    public Object visitSkipBracedBlock(KeYParser.SkipBracedBlockContext ctx) {
        LBRACE
        {
            int nestingLevel = 1;
            recLoop:
            while (true) {
                switch (input.LA(1)) {
                    case LBRACE:
                        nestingLevel++;
                        break;

                    case RBRACE:
                        nestingLevel--;
                        if (nestingLevel == 0) break recLoop;
                        break;
                }
                input.consume();
            }
        }
        RBRACE
    }

    @Override
    public Object visitProblem(KeYParser.ProblemContext ctx) {
        problem returns[ Term _problem = null]
        @init {
            boolean axiomMode = false;
            int beginPos = 0;
            choices = DefaultImmutableSet.<Choice>nil();
            chooseContract = this.chooseContract;
            proofObligation = this.proofObligation;
        }
        @after {
            _problem = a;
            this.chooseContract = chooseContract;
            this.proofObligation = proofObligation;
        }
        :

        profile

                (pref = preferences)
        {
            beginPos = input.index();
        }

        string = bootClassPath
        // the result is of no importance here (strange enough)

        stlist = classPaths
        string = javaSource

        decls
        {
            if (parse_includes || onlyWith) return null;
            switchToNormalMode();
        }

        // WATCHOUT: choices is always going to be an empty set here,
        // isn't it?
        (contracts) *
                (invariants) *
                ((RULES {
            axiomMode = false;
        }
        |AXIOMS {
            axiomMode = true;
        }
        )

        (choices = option_list[choices]) ?
                (
                        // #MT-1185: KeY parses the same file several times.
                        // During problem parsing, some aspects of taclets
                        // can not be reparsed. Hence, in the problem walkthrough
                        // crudely overread the taclet setcion altogether.
                        {skip_taclets} ? = >
                        skipBracedBlock
                        |
                        LBRACE
        {
            switchToSchemaMode();
        }
        (
                s = taclet[choices, axiomMode]SEMI
        {
            if (!skip_taclets) {
                final RuleKey key = new RuleKey(s);
                if (taclets.containsKey(key)) {
                    semanticError
                            ("Cannot add taclet \"" + s.name() +
                                    "\" to rule base as a taclet with the same " +
                                    "name already exists.");

                } else {
                    taclets.put(key, s);
                }
            }
        }
        )*
        RBRACE {
            choices = DefaultImmutableSet.<Choice>nil();
        }
        )
        )*

        {
            if (input.index() == 0) {
                problemHeader = "";
            } else {
                problemHeader = lexer.toString(beginPos, input.index() - 1);
            }
        }

        ((PROBLEM LBRACE
        {
            switchToNormalMode();
        }
        a = formula
        RBRACE)
        |
        CHOOSECONTRACT(chooseContract = string_literal SEMI) ?
                {
        if (chooseContract == null) {
            chooseContract = "";
        }
        }
        |
        PROOFOBLIGATION(proofObligation = string_literal SEMI) ?
                {
        if (proofObligation == null) {
            proofObligation = "";
        }
        }
        )?
        ;
    }

    @Override
    public String visitBootClassPath(KeYParser.BootClassPathContext ctx) {
        return ctx.string_literal() != null ? ctx.string_literal().getText() : null;
    }

    @Override
    public String visitClassPaths(KeYParser.ClassPathsContext ctx) {
        if (ctx.NODEFAULTCLASSES() != null) {
            throwEx(new NoViableAltException(
                    "\\noDefaultClasses is no longer supported. " +
                            "Use \\bootclasspath. See docs/README.classpath", -1, -1, input));
        }
        return ctx.getText();
    }

    @Override
    public String visitJavaSource(KeYParser.JavaSourceContext ctx) {
        return ctx.oneJavaSource() != null ? (String) visit(ctx.oneJavaSource()) : null;
    }

    @Override
    public String visitOneJavaSource(KeYParser.OneJavaSourceContext ctx) {
        return ctx.getText();
    }

    @Override
    public Object visitProfile(KeYParser.ProfileContext ctx) {
        profileName = (String) visit(ctx.profileName);
        return null;
    }

    @Override
    public String visitPreferences(KeYParser.PreferencesContext ctx) {
        return ctx.s != null ? (String) visit(ctx.s) : null;
    }

    @Override
    public Triple<String, Integer, Integer> visitProofScript(KeYParser.ProofScriptContext ctx) {
        int line = ctx.ps.getLine();
        // +1 for antlr starting at 0
        // +1 for removing the leading "
        int col = ctx.ps.getCharPositionInLine() + 2;
        String content = ctx.ps.getText().substring(1, ctx.ps.getText().length() - 1);
        return new Triple<String, Integer, Integer>(content, line, col);
    }

    /*
    @Override
    public Object visitProof(KeYParser.ProofContext ctx) {
        return super.visitProof(ctx);
    }

    @Override
    public Object visitProofBody(KeYParser.ProofBodyContext ctx) {
        return super.visitProofBody(ctx);
    }

    @Override
    public Object visitPseudosexpr(KeYParser.PseudosexprContext ctx) {
        proofElementId=expreid
                (str = string_literal )?
                { prl.beginExpr(proofElementId,str); }
        ( pseudosexpr[prl] )* )
        { prl.endExpr(proofElementId, stringLiteralLine); }
        return null;
    }

    @Override
    public IProofFileParser.ProofElementID visitExpreid(KeYParser.ExpreidContext ctx) {
        return prooflabel2tag.get(visitSimple_ident(ctx.simple_ident()));
    }*/
}
