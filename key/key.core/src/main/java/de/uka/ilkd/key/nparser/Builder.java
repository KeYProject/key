package de.uka.ilkd.key.nparser;

import antlr.RecognitionException;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.visitor.DeclarationProgramVariableCollector;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.parser.*;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.IProofFileParser;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.conditions.*;
import de.uka.ilkd.key.rule.tacletbuilder.*;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.dl.translation.DLSpecFactory;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import org.antlr.runtime.NoViableAltException;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.*;

import java.io.File;
import java.math.BigInteger;
import java.util.*;
import java.util.stream.Collectors;

import static de.uka.ilkd.key.proof.io.IProofFileParser.ProofElementID;

@SuppressWarnings("unchecked")
public class Builder extends KeYParserBaseVisitor<Object> {
    //region

    // This is used for testing in TestTermParserHeap.java
    public static final String NO_HEAP_EXPRESSION_BEFORE_AT_EXCEPTION_MESSAGE
            = "Expecting select term before '@', not: ";
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
    private TacletBuilder b;
    private boolean ldt = false;
    private String currentChoiceCategory;
    private boolean ruleWithFind;
    private boolean negated;
    private NamespaceSet nss;
    private Namespace<SchemaVariable> schemaVariablesNamespace;
    private HashMap<String, String> category2Default = new LinkedHashMap<>();
    private boolean onlyWith = false;
    private ImmutableSet<Choice> activatedChoices = DefaultImmutableSet.nil();
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
    //private int savedGuessing = -1;
    private int lineOffset = 0;
    private int colOffset = 0;
    //private int stringLiteralLine = 0; // HACK!
    private Services services;
    private JavaReader javaReader;
    // if this is used then we can capture parts of the input for later use
    private IProgramMethod pm = null;
    private LinkedHashMap<RuleKey, Taclet> taclets = new LinkedHashMap<RuleKey, Taclet>();
    private ImmutableList<Contract> contracts = ImmutableSLList.nil();
    private ImmutableSet<ClassInvariant> invs = DefaultImmutableSet.nil();
    private ParserConfig schemaConfig;
    private ParserConfig normalConfig;
    // the current active config
    private ParserConfig parserConfig;
    private Term quantifiedArrayGuard = null;
    private String profileName;
    private ParsableVariable selfVar;
    private boolean checkSort;
    private SchemaVariableModifierSet mods;
    private boolean primitiveElementType;
    private boolean isPrimitive;
    private boolean axiomMode;
    //region stack handling
    private Stack<Object> parameters = new Stack<>();

    /* Most general constructor, should only be used internally */
    private Builder(Services services,
                    NamespaceSet nss,
                    ParserMode mode) {
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
                   JavaReader jr,
                   Services services,
                   NamespaceSet nss,
                   AbbrevMap scm) {
        this(services, nss, mode);
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
                   Services services,
                   NamespaceSet nss) {
        this(mode,
                new SchemaRecoder2KeY(services, nss),
                services,
                nss,
                new AbbrevMap());
    }

    /**
     * Used to construct Taclet parser
     */
    public Builder(ParserMode mode,
                   SchemaJavaReader jr,
                   Services services,
                   NamespaceSet nss,
                   HashMap taclet2Builder) {
        this(services, nss, mode);
        switchToSchemaMode();
        this.scm = new AbbrevMap();
        this.javaReader = jr;
        this.taclet2Builder = taclet2Builder;
    }

    /**
     * Used to construct Problem parser
     */
    public Builder(ParserMode mode,
                   ParserConfig schemaConfig,
                   ParserConfig normalConfig,
                   HashMap taclet2Builder,
                   ImmutableList<Taclet> taclets) {
        this(null, null, mode);
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

    private static boolean isSelectTerm(Term term) {
        return term.op().name().toString().endsWith("::select") && term.arity() == 3;
    }

    private <T> T oneOf(ParserRuleContext... ctxs) {
        for (ParserRuleContext ctx : ctxs) {
            if (ctx != null) {
                return (T) ctx.accept(this);
            }
        }
        return null;
    }

    private <T> List<T> allOf(Collection<? extends ParserRuleContext> argument) {
        return argument.stream().map(it -> (T) it.accept(this)).collect(Collectors.toList());
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
        ImmutableList<Taclet> result = ImmutableSLList.nil();

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

    private Term toZNotation(String literal, Namespace<Function> functions) {
        literal = literal.replace("_", "");
        final boolean negative = (literal.charAt(0) == '-');
        if (negative) {
            literal = literal.substring(1);
        }
        int base = 10;

        if (literal.startsWith("0x")) {
            literal = literal.substring(2);
            base = 16;
        }

        if (literal.startsWith("0b")) {
            literal = literal.substring(2);
            base = 8;
        }

        BigInteger bi = new BigInteger(literal, base);
        return toZNotation(bi, functions);
    }

    private Term toZNotation(BigInteger bi, Namespace<Function> functions) {
        boolean negative = bi.signum() < 0;
        String s = bi.abs().toString();
        Term result = getTermFactory().createTerm(
                functions.lookup(new Name("#")));

        for (int i = 0; i < s.length(); i++)
            result = getTermFactory().createTerm(
                    functions.lookup(new Name(s.substring(i, i + 1))), result);

        if (negative) {
            result = getTermFactory().createTerm(
                    functions.lookup(new Name("neglit")), result);
        }
        return getTermFactory().createTerm(
                functions.lookup(new Name("Z")), result);
    }

    private String getTypeList(ImmutableList<ProgramVariable> vars) {
        StringBuffer result = new StringBuffer();
        final Iterator<ProgramVariable> it = vars.iterator();
        while (it.hasNext()) {
            result.append(it.next().getContainerType().getFullName());
            if (it.hasNext()) result.append(", ");
        }
        return result.toString();
    }

    private Operator getAttributeInPrefixSort(Sort prefixSort, String attributeName) {
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
                    throwEx(new KeYSemanticException(null, getSourceName(), ex));
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

        if (result == null && !("length" .equals(attributeName))) {
            throwEx(new NotDeclException(null, "Attribute ", attributeName));
        }
        return result;
    }

    public Term createAttributeTerm(Term prefix, Operator attribute) {
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

    private KeYJavaType getTypeByClassName(String s) {
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

    private PairOfStringAndJavaBlock getJavaBlock(Token t) {
        PairOfStringAndJavaBlock sjb = new PairOfStringAndJavaBlock();
        String s = t.getText();
        //int index = s.indexOf("\n");
        //sjb.opName = s.substring(0, index);
        //s = s.substring(index + 1);
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
            throwEx(new RecognitionException(input));
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
                throwEx(new RecognitionException(input));
                //throw new JavaParserException(e.getMessage(), t.getText(), getSourceName(), t.getLine(), t.getCharPositionInLine(), -1, -1);  // row/columns already in text
            }
            if (e.proofJavaException() != null
                    && e.proofJavaException().currentToken != null
                    && e.proofJavaException().currentToken.next != null) {
                lineOffset = e.proofJavaException().currentToken.next.beginLine - 1;
                colOffset = e.proofJavaException().currentToken.next.beginColumn;
                e.proofJavaException().currentToken.next.beginLine = getLine();
                e.proofJavaException().currentToken.next.beginColumn = getColumn();
                throwEx(new RecognitionException(input));
                //throw  new JavaParserException(e.getMessage(), t.getText(), getSourceName(), t.getLine(), t.getCharPositionInLine(), lineOffset, colOffset);

            }
            throwEx(new RecognitionException(input));
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
        Sort result = sorts().lookup(new Name(name));
        if (result == null) {
            if (name.equals(NullSort.NAME.toString())) {
                Sort objectSort
                        = sorts().lookup(new Name("java.lang.Object"));
                if (objectSort == null) {
                    semanticError("Null sort cannot be used before "
                            + "java.lang.Object is declared");
                }
                result = new NullSort(objectSort);
                sorts().add(result);
            } else {
                result = sorts().lookup(new Name("java.lang." + name));
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
        v = programVariables().lookup
                (new ProgramElementName(varfunc_name));
        if (v != null && args == null) {
            return v;
        }

        // case 3: function
        v = functions().lookup(new Name(varfunc_name));
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
                    (null, "(program) variable or constant", varfunc_name);
        } else {
            throw new NotDeclException
                    (null, "function or static query", varfunc_name);
        }
    }

    private boolean isStaticAttribute() {
        //TODO reimplement without lexer `input`
        if (inSchemaMode()) return false;
        final JavaInfo javaInfo = getJavaInfo();
        KeYJavaType kjt = null;
        boolean result = false;
//        try {
        int n = 1;
        StringBuffer className = new StringBuffer();
        /*StringBuffer className = new StringBuffer(input.LT(n).getText());
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
        }*/
        kjt = getTypeByClassName(className.toString());

        if (kjt != null) {
            // works as we do not have inner classes
            /*if (input.LA(n + 1) == KeYLexer.DOT) {
                final ProgramVariable pv =
                        javaInfo.getAttribute(input.LT(n + 2).getText(), kjt);
                result = (pv != null && pv.isStatic());
            }*/
        } else {
            result = false;
        }
        return result;
    }

    /*private boolean isTermTransformer()  {
        return (input.LA(1) == KeYLexer.IDENT &&
                AbstractTermTransformer.name2metaop(input.LT(1).getText()) != null)
                || input.LA(1) == KeYLexer.IN_TYPE;
    }

    private boolean isStaticQuery() {
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
*/
    private TacletBuilder createTacletBuilderFor(Object find, int applicationRestriction) {
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
        return b;
    }

    private void addGoalTemplate(TacletBuilder b,
                                 String id,
                                 Object rwObj,
                                 Sequent addSeq,
                                 ImmutableList<Taclet> addRList,
                                 ImmutableSet<SchemaVariable> pvs,
                                 ImmutableSet<Choice> soc) {
        TacletGoalTemplate gt = null;
        if (rwObj == null) {
            // there is no replacewith, so we take
            gt = new TacletGoalTemplate(addSeq,
                    addRList,
                    pvs);
        } else {
            if (b instanceof NoFindTacletBuilder) {
                // there is a replacewith without a find.
                throwEx(new RecognitionException(""));
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
                    throwEx(new UnfittingReplacewithException
                            ("Replacewith in a Antec-or SuccTaclet has " +
                                    "to contain a sequent (not a term)",
                                    getSourceName(), getLine(), getColumn()));
                }
            } else if (b instanceof RewriteTacletBuilder) {
                if (rwObj instanceof Term) {
                    gt = new RewriteTacletGoalTemplate(addSeq,
                            addRList,
                            (Term) rwObj,
                            pvs);
                } else {
                    throwEx(new UnfittingReplacewithException
                            ("Replacewith in a RewriteTaclet has " +
                                    "to contain a term (not a sequent)",
                                    getSourceName(), getLine(), getColumn()));
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

    private ImmutableSet<Modality> lookupOperatorSV(String opName, ImmutableSet<Modality> modalities) {
        SchemaVariable sv = schemaVariables().lookup(new Name(opName));
        if (sv == null || !(sv instanceof ModalOperatorSV)) {
            semanticError("Schema variable " + opName + " not defined.");
        }
        ModalOperatorSV osv = (ModalOperatorSV) sv;
        modalities = modalities.union(osv.getModalities());
        return modalities;
    }

    private ImmutableSet<Modality> opSVHelper(String opName, ImmutableSet<Modality> modalities) {
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
        throw new RuntimeException(message);
    }

    private boolean isImplicitHeap(Term t) {
        return getServices().getTermBuilder().getBaseHeap().equals(t);
    }

    private Term replaceHeap(Term term, Term heap, int depth) {
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
                throwEx(new RecognitionException());
            }

        }
        return term;
    }

    /*
     * Replace standard heap by another heap in an observer function.
     */
    protected Term heapSelectionSuffix(Term term, Term heap) {

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
        return oneOf(ctx.decls(), ctx.problem(), ctx.proof());
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        if (parse_includes)
            allOf(ctx.one_include_statement());
        activatedChoices = DefaultImmutableSet.nil();
        accept(ctx.options_choice());
        allOf(ctx.option_decls());
        allOf(ctx.sort_decls());
        allOf(ctx.prog_var_decls());
        allOf(ctx.schema_var_decls());
        allOf(ctx.pred_decls());
        allOf(ctx.func_decls());
        allOf(ctx.transform_decls());
        allOf(ctx.ruleset_decls());
        return null;
    }

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
        allOf(ctx.activated_choice());
        return null;
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
            throwEx(new NotDeclException(null, "Option", ch));
        } else {
            activatedChoices = activatedChoices.add(c);
        }
        return null;
    }

    @Override
    public Object visitOption_decls(KeYParser.Option_declsContext ctx) {
        return allOf(ctx.choice());
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
        String name = currentChoiceCategory + ":" + ctx.choice_.getText();
        Choice c = choices().lookup(new Name(name));
        if (c == null) {
            c = new Choice(ctx.choice_.getText(), currentChoiceCategory);
            choices().add(c);
        }
        if (!category2Default.containsKey(currentChoiceCategory)) {
            category2Default.put(currentChoiceCategory, name);
        }
        return c;
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
        return null;
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
        return null;
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
                        ImmutableSet<Sort> ext = DefaultImmutableSet.nil();
                        ImmutableSet<Sort> oneOf = DefaultImmutableSet.nil();

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
                        ImmutableSet<Sort> ext = DefaultImmutableSet.nil();

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
    public Term visitString_literal(KeYParser.String_literalContext ctx) {
        String s = unescapeString(ctx.id.getText());
        return getServices().getTypeConverter()
                .convertToLogicElement(new StringLiteral(s));
        //var lit = unescapeString(ctx.id.getText());
        //lit = lit.substring(1, lit.length() - 1);
        //return lit;
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
        switchToSchemaMode();
        List<SchemaVariable> seq = allOf(ctx.one_schema_var_decl());
        switchToNormalMode();
        return seq;
    }

    @Override
    public Object visitOne_schema_var_decl(KeYParser.One_schema_var_declContext ctx) {
        //TODO
        boolean makeVariableSV = false;
        boolean makeSkolemTermSV = false;
        boolean makeTermLabelSV = false;
        SchemaVariableModifierSet mods = null;
        accept(ctx.one_schema_modal_op_decl());
        Sort s = null;
        List<String> ids = accept(ctx.simple_ident_comma_list());
        if (ctx.PROGRAM() != null) {
            mods = new SchemaVariableModifierSet.ProgramSV();
            accept(ctx.schema_modifiers());
            String id = accept(ctx.id);
            String nameString = accept(ctx.nameString);
            String parameter = accept(ctx.simple_ident_dots());
            if (nameString != null && !"name" .equals(nameString)) {
                semanticError("Unrecognized token '" + nameString + "', expected 'name'");
            }
            ProgramSVSort psv = ProgramSVSort.name2sort().get(new Name(id));
            s = parameter != null ? psv.createInstance(parameter) : psv;
            if (s == null) {
                semanticError
                        ("Program SchemaVariable of type " + id + " not found.");
            }
            //List<String> ids = accept(ctx.simple_ident_comma_list());
            //TODO
        }
        if (ctx.FORMULA() != null) {
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers());
            s = Sort.FORMULA;
        }
        if (ctx.TERMLABEL() != null) {
            makeTermLabelSV = true;
            mods = new SchemaVariableModifierSet.TermLabelSV();
            accept(ctx.schema_modifiers());
        }
        if (ctx.UPDATE() != null) {
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers());
            s = Sort.UPDATE;
        }
        if (ctx.SKOLEMFORMULA() != null) {
            makeSkolemTermSV = true;
            mods = new SchemaVariableModifierSet.FormulaSV();
            accept(ctx.schema_modifiers());
            s = Sort.FORMULA;
        }
        if (ctx.TERM() != null) {
            mods = new SchemaVariableModifierSet.TermSV();
            accept(ctx.schema_modifiers());
        }
        if (ctx.VARIABLE() != null || ctx.VARIABLES() != null) {
            makeVariableSV = true;
            mods = new SchemaVariableModifierSet.VariableSV();
            accept(ctx.schema_modifiers());
        }
        if (ctx.SKOLEMTERM() != null) {
            makeSkolemTermSV = true;
            mods = new SchemaVariableModifierSet.SkolemTermSV();
            accept(ctx.schema_modifiers());
        }
        s = accept(ctx.any_sortId_check());

        try {
            for (String id : ids) {
                schema_var_decl(id,
                        s,
                        makeVariableSV,
                        makeSkolemTermSV,
                        makeTermLabelSV,
                        mods);
            }
        } catch (AmbigiousDeclException e) {
            throwEx(e);
        }
        return null;
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
        ImmutableSet<Modality> modalities = DefaultImmutableSet.nil();
        Sort sort = accept(ctx.any_sortId_check());
        if (sort != Sort.FORMULA) {
            semanticError("Modal operator SV must be a FORMULA, not " + sort);
        }
        List<String> ids = accept(ctx.simple_ident_comma_list());
        String id = accept(ctx.simple_ident());

        if (skip_schemavariables) {
            return null;
        }

        for (String s : ids) {
            modalities = opSVHelper(s, modalities);
        }
        SchemaVariable osv = schemaVariables().lookup(new Name(id));
        if (osv != null)
            semanticError("Schema variable " + id + " already defined.");

        osv = SchemaVariableFactory.createModalOperatorSV(new Name(id), sort, modalities);

        if (inSchemaMode()) {
            schemaVariables().add(osv);
            //functions().add(osv);
        }
        return null;
    }

    @Override
    public Object visitPred_decl(KeYParser.Pred_declContext ctx) {
        String pred_name = accept(ctx.funcpred_name());
        List<Boolean> whereToBind = accept(ctx.where_to_bind());
        List<Sort> argSorts = accept(ctx.arg_sorts());
        if (!skip_predicates) {
            if (whereToBind != null && whereToBind.size() != argSorts.size()) {
                semanticError("Where-to-bind list must have same length "
                        + "as argument list");
            }

            Function p = null;

            int separatorIndex = pred_name.indexOf("::");
            if (separatorIndex > 0) {
                String sortName = pred_name.substring(0, separatorIndex);
                String baseName = pred_name.substring(separatorIndex + 2);
                Sort genSort = lookupSort(sortName);
                if (genSort instanceof GenericSort) {
                    p = SortDependingFunction.createFirstInstance(
                            (GenericSort) genSort,
                            new Name(baseName),
                            Sort.FORMULA,
                            (Sort[]) argSorts.toArray(),
                            false);
                }
            }

            if (p == null) {
                p = new Function(new Name(pred_name),
                        Sort.FORMULA,
                        (Sort[]) argSorts.toArray(),
                        (Boolean[]) whereToBind.toArray(),
                        false);
            }
            if (lookup(p.name()) != null) {
                if (!isProblemParser()) {
                    throwEx(new AmbigiousDeclException(p.name().toString(),
                            getSourceName(),
                            getLine(),
                            getColumn()));

                }
            } else {
                addFunction(p);
            }
        }
        return null;
    }

    @Override
    public Object visitPred_decls(KeYParser.Pred_declsContext ctx) {
        return allOf(ctx.pred_decl());
    }

    @Override
    public Integer visitLocation_ident(KeYParser.Location_identContext ctx) {
        var id = visit(ctx.simple_ident());
        if ("Location" .equals(id)) {
            return LOCATION_MODIFIER;
        } else if (!"Location" .equals(id)) {
            semanticError(
                    id + ": Attribute of a Non Rigid Function can only be 'Location'");
        }
        return NORMAL_NONRIGID;
    }

    @Override
    public Object visitFunc_decl(KeYParser.Func_declContext ctx) {
        boolean unique = ctx.UNIQUE() != null;
        Sort retSort = accept(ctx.any_sortId_check());
        String func_name = accept(ctx.funcpred_name());
        List<Boolean[]> whereToBind = accept(ctx.where_to_bind());
        List<Sort> argSorts = accept(ctx.arg_sorts());
        if (!skip_functions) {
            if (whereToBind != null && whereToBind.size() != argSorts.size()) {
                semanticError("Where-to-bind list must have same length "
                        + "as argument list");
            }

            Function f = null;
            int separatorIndex = func_name.indexOf("::");
            if (separatorIndex > 0) {
                String sortName = func_name.substring(0, separatorIndex);
                String baseName = func_name.substring(separatorIndex + 2);
                Sort genSort = lookupSort(sortName);
                if (genSort instanceof GenericSort) {
                    f = SortDependingFunction.createFirstInstance(
                            (GenericSort) genSort,
                            new Name(baseName),
                            retSort,
                            (Sort[]) argSorts.toArray(),
                            unique);
                }
            }

            if (f == null) {
                f = new Function(new Name(func_name),
                        retSort,
                        (Sort[]) argSorts.toArray(),
                        (Boolean[]) whereToBind.toArray(),
                        unique);
            }

            if (lookup(f.name()) != null) {
                if (!isProblemParser()) {
                    throwEx(new AmbigiousDeclException(f.name().toString(),
                            getSourceName(), getLine(), getColumn()));
                }
            } else {
                addFunction(f);
            }
            return f;
        }
        return null;
    }

    @Override
    public Object visitFunc_decls(KeYParser.Func_declsContext ctx) {
        return allOf(ctx.func_decl());
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
        return allOf(ctx.transform_decl());
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
        return null;
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
                throwEx(new NotDeclException(null, "sort", name));
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
        Term a = accept(ctx.term());
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
        return accept(ctx.term());
    }

    @Override
    public Term visitElementary_update_term(KeYParser.Elementary_update_termContext ctx) {
        List<Term> terms = mapOf(ctx.equivalence_term());
        if (terms.size() == 1)
            return terms.get(0);
        else
            return getServices().getTermBuilder().elementary(terms.get(0), terms.get(1));
    }

    @Override
    public Term visitEquivalence_term(KeYParser.Equivalence_termContext ctx) {
        List<Term> terms = mapOf(ctx.implication_term());
        return getTermFactory().createTerm(Equality.EQV, terms);
    }

    @Override
    public Term visitImplication_term(KeYParser.Implication_termContext ctx) {
        Term a = accept(ctx.a);
        Term a1 = accept(ctx.a1);
        if (a1 == null) return a;
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
        return (Term) oneOf(ctx.unary_formula(), ctx.equality_term());
    }

    @Override
    public Term visitUnary_formula(KeYParser.Unary_formulaContext ctx) {
        if (ctx.NOT() != null) {
            return getTermFactory().createTerm(Junctor.NOT, (Term) accept(ctx.term60()));
        }
        return oneOf(ctx.modality_dl_term(), ctx.quantifierterm());
    }

    @Override
    public Object visitEquality_term(KeYParser.Equality_termContext ctx) {
        Term a = accept(ctx.a);
        if (ctx.EQUALS() == null && null == ctx.NOT_EQUALS()) {
            return a;
        }

        boolean negated = ctx.NOT_EQUALS() != null;
        Term b = accept(ctx.a1);
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
        Term a = accept(ctx.a);
        if (ctx.op == null) return a;
        Function op = (Function) visit(ctx.op);
        Term a1 = accept(ctx.a1);
        return getTermFactory().createTerm(op, a, a1);
    }

    @Override
    public Object visitWeak_arith_op_term(KeYParser.Weak_arith_op_termContext ctx) {
        Term a = accept(ctx.a);
        if (ctx.op == null) return a;
        Function op = (Function) visit(ctx.op);
        Term a1 = accept(ctx.a1);
        return getTermFactory().createTerm(op, a, a1);
    }

    @Override
    public Object visitStrong_arith_op_term(KeYParser.Strong_arith_op_termContext ctx) {
        Term a = accept(ctx.a);
        if (ctx.op == null) return a;
        Function op = (Function) visit(ctx.op);
        Term a1 = accept(ctx.a1);
        return getTermFactory().createTerm(op, a, a1);
    }

    @Override
    public Term visitTerm110(KeYParser.Term110Context ctx) {
        return (Term) oneOf(ctx.braces_term(), ctx.accessterm());
    }

    @Override
    public Object visitStaticAttributeOrQueryReference(KeYParser.StaticAttributeOrQueryReferenceContext ctx) {
        //TODO weigl: this rule is a total grammar blower.
        String attrReference = ctx.id.getText();
        for (int i = 0; i < ctx.EMPTYBRACKETS().size(); i++) {
            attrReference += "[]";
        }

        /*KeYJavaType kjt = null;
        kjt = getTypeByClassName(attrReference);
        if (kjt == null) {
            throwEx(new NotDeclException(input, "Class", attrReference));
        }
        attrReference = kjt.getSort().name().toString();
        match(input, DOT, null);
            attrReference += "::" + input.LT(1).getText();
            match(input, IDENT, null);
            if(savedGuessing > -1) {
                state.backtracking = savedGuessing;
                savedGuessing = -1;
            }*/
        return attrReference;
    }

    @Override
    public Term visitStatic_attribute_suffix(KeYParser.Static_attribute_suffixContext ctx) {
        Operator v = null;
        String attributeName = accept(ctx.staticAttributeOrQueryReference());
        String className;
        if (attributeName.indexOf(':') != -1) {
            className =
                    attributeName.substring(0, attributeName.indexOf(':'));
        } else {
            className =
                    attributeName.substring(0, attributeName.lastIndexOf("."));
        }
        v = getAttributeInPrefixSort(getTypeByClassName(className).getSort(), attributeName);
        return createAttributeTerm(null, v);
    }

    private <T> T pop() {
        return (T) parameters.pop();
    }

    public <T> @Nullable T accept(@Nullable ParserRuleContext ctx, Object... args) {
        int stackSize = parameters.size();
        for (Object a : args) parameters.push(a);
        T t = accept(ctx);
        //Stack hygiene
        while (parameters.size() > stackSize) {
            parameters.pop();
        }
        return t;
    }
    //endregion

    /**
     * stack parameter: (prefix : Term)
     *
     * @param ctx
     * @return
     */
    @Override
    public Term visitAttribute_or_query_suffix(KeYParser.Attribute_or_query_suffixContext ctx) {
        Term prefix = pop();
        Term result = null;
        if (ctx.STAR() != null) {
            return services.getTermBuilder().allFields(prefix);
        }

        String memberName = accept(ctx.memberName);
        if (ctx.query_suffix() != null) {
            result = accept(ctx.query_suffix());
            assert result != null;
        }

        if (result == null) {
            if (prefix.sort() == getServices().getTypeConverter().getSeqLDT().targetSort()) {
                if ("length" .equals(memberName)) {
                    result = getServices().getTermBuilder().seqLen(prefix);
                } else {
                    semanticError("There is no attribute '" + memberName +
                            "' for sequences (Seq), only 'length' is supported.");
                }
            } else {
                Operator v = getAttributeInPrefixSort(prefix.sort(), memberName);
                result = createAttributeTerm(prefix, v);
            }
        }
        return result;
    }

    @Override
    public String visitAttrid(KeYParser.AttridContext ctx) {
        return ctx.getText();
        /*if(ctx.LPAREN()!=null){
           STring clss = accept(ctx.sort_name());
            id2 = simple_ident RPAREN
            return clss + "::" + id2;;
        }

        return  accept(ctx.simple_ident());
        */
    }

    /**
     * stack parameters: (prefix : Term, memberName : String)
     *
     * @param ctx
     * @return
     */
    @Override
    public Object visitQuery_suffix(KeYParser.Query_suffixContext ctx) {
        Term prefix = pop();
        String memberName = pop();
        String classRef, name;
        boolean brackets = false;
        List<Term> args = accept(ctx.argument_list());
        // true in case class name is not explicitly mentioned as part of memberName
        boolean implicitClassName = memberName.indexOf("::") == -1;

        if (implicitClassName) {
            classRef = prefix.sort().name().toString();
            name = memberName;
        } else {
            String[] parts = memberName.split("::", 2);
            classRef = parts[0];
            name = parts[1];
        }
        KeYJavaType kjt = getTypeByClassName(classRef);
        if (kjt == null)
            throwEx(new NotDeclException(null, "Class", classRef));
        classRef = kjt.getFullName();

        return getServices().getJavaInfo().getProgramMethodTerm(prefix, name,
                (Term[]) args.toArray(), classRef, implicitClassName);
    }

    @Override
    public Object visitAccessterm(KeYParser.AccesstermContext ctx) {
        int selectNestingDepth = globalSelectNestingDepth;
        final Sort objectSort = getServices().getJavaInfo().objectSort();

        Term result = null;
        if (ctx.MINUS() != null) {
            result = accept(ctx.term110());
            if (result.sort() != Sort.FORMULA) {
                return getTermFactory().createTerm(
                        functions().lookup(new Name("neg")), result);
            } else {
                semanticError("Formula cannot be prefixed with '-'");
            }
        }

        if (ctx.any_sortId_check() != null) {
            Sort s = accept(ctx.any_sortId_check());
            if (s == null) {
                semanticError("Tried to cast to unknown type.");
            } else if (objectSort != null
                    && !s.extendsTrans(objectSort)
                    && result.sort().extendsTrans(objectSort)) {
                semanticError("Illegal cast from " + result.sort() +
                        " to sort " + s +
                        ". Casts between primitive and reference types are not allowed. ");
            }
            return getTermFactory().createTerm(
                    s.getCastSymbol(getServices()), result);
        }

        var a = oneOf(ctx.static_query(),
                ctx.static_attribute_suffix(),
                ctx.atom());

        //TODO losing order
        var suffix = allOf(ctx.accessterm_bracket_suffix());
        var attr = allOf(ctx.attribute_or_query_suffix());

        if (ctx.heap_selection_suffix() != null) {
            accept(ctx.heap_selection_suffix());
        }
        return a;
    }

    /**
     * stack parameter: (term : Term)
     *
     * @param ctx
     * @return
     */
    @Override
    public Term visitHeap_selection_suffix(KeYParser.Heap_selection_suffixContext ctx) {
        return heapSelectionSuffix(pop(), accept(ctx.heap));
    }

    @Override
    public Object visitAccessterm_bracket_suffix(KeYParser.Accessterm_bracket_suffixContext ctx) {
        //Todo this rule is context-sensitive
        Term reference = pop();

/*        isHeapTerm(reference) }? tmp = heap_update_suffix[reference] { $result = tmp; }
    | { isSequenceTerm(reference) }? tmp = seq_get_suffix[reference] { $result = tmp; }
    | tmp = array_access_suffix[reference] { $result = tmp; $increaseHeapSuffixCounter = true; }*/
        return reference;
    }


    @Override
    public Object visitSeq_get_suffix(KeYParser.Seq_get_suffixContext ctx) {
        Term reference = pop();
        Term indexTerm = accept(ctx.logicTermReEntry());
        if (!isIntTerm(indexTerm))
            semanticError("Expecting term of sort " + IntegerLDT.NAME + " as index of sequence " + reference + ", but found: " + indexTerm);
        return getServices().getTermBuilder().seqGet(Sort.ANY, reference, indexTerm);
    }

    @Override
    public Object visitStatic_query(KeYParser.Static_queryContext ctx) {
        String queryRef = accept(ctx.staticAttributeOrQueryReference());
        List<Term> args = accept(ctx.argument_list());
        int index = queryRef.indexOf(':');
        String className = queryRef.substring(0, index);
        String qname = queryRef.substring(index + 2);
        Term result = getServices().getJavaInfo().getStaticProgramMethodTerm(qname, (Term[]) args.toArray(), className);
        if (result == null && isTermParser()) {
            final Sort sort = lookupSort(className);
            if (sort == null) {
                semanticError("Could not find matching sort for " + className);
            }
            KeYJavaType kjt = getServices().getJavaInfo().getKeYJavaType(sort);
            if (kjt == null) {
                semanticError("Found logic sort for " + className +
                        " but no corresponding java type!");
            }
        }
        return result;
    }

    @Override
    public Object visitHeap_update_suffix(KeYParser.Heap_update_suffixContext ctx) {
        Term heap = pop();
        // XXX find the right kind of non-terminal for "o.f" and "a[i]"
        // and do not resign to parsing an arbitrary term
        if (ctx.ASSIGN() != null) {
            Term target = accept(ctx.target);
            Term val = accept(ctx.val);
            Term objectTerm = target.sub(1);
            Term fieldTerm = target.sub(2);
            return getServices().getTermBuilder().store(heap, objectTerm, fieldTerm, val);
        } else {
            String id = accept(ctx.simple_ident());
            List<Term> args = accept(ctx.args);
            Function f = functions().lookup(new Name(id));
            if (f == null) {
                semanticError("Unknown heap constructor " + id);
            }
            Term[] augmentedArgs = new Term[args.size() + 1];
            System.arraycopy(args, 0, augmentedArgs, 1, args.size());
            augmentedArgs[0] = heap;
            Term result = getTermFactory().createTerm(f, augmentedArgs);
            if (!result.sort().name().toString().equals("Heap")) {
                semanticError(id + " is not a heap constructor ");
            }
            return result;
        }
    }

    @Override
    public Object visitArray_access_suffix(KeYParser.Array_access_suffixContext ctx) {
        Term indexTerm = null, rangeFrom = null, rangeTo = null;
        Term result = pop();

        if (ctx.STAR() != null) {
            rangeFrom = toZNotation("0", functions());
            Term lt = getServices().getTermBuilder().dotLength(result);
            Term one = toZNotation("1", functions());
            rangeTo = getTermFactory().createTerm
                    (functions().lookup(new Name("sub")), lt, one);
        } else {
            indexTerm = accept(ctx.indexTerm);
            rangeFrom = accept(ctx.rangeTo);
        }
        if (rangeTo != null) {
            if (quantifiedArrayGuard == null) {
                semanticError(
                        "Quantified array expressions are only allowed in locations.");
            }
            LogicVariable indexVar = new LogicVariable(new Name("i"),
                    sorts().lookup(new Name("int")));
            indexTerm = getTermFactory().createTerm(indexVar);

            Function leq = functions().lookup(new Name("leq"));
            Term fromTerm = getTermFactory().createTerm(leq, rangeFrom, indexTerm);
            Term toTerm = getTermFactory().createTerm(leq, indexTerm, rangeTo);
            Term guardTerm = getTermFactory().createTerm(Junctor.AND, fromTerm, toTerm);
            quantifiedArrayGuard = getTermFactory().createTerm(Junctor.AND, quantifiedArrayGuard, guardTerm);
        }
        return getServices().getTermBuilder().dotArr(result, indexTerm);
    }

    @Override
    public Object visitBoolean_constant(KeYParser.Boolean_constantContext ctx) {
        if (ctx.TRUE() != null)
            return getTermFactory().createTerm(Junctor.TRUE);
        else
            return getTermFactory().createTerm(Junctor.FALSE);
    }

    @Override
    public Object visitAtom(KeYParser.AtomContext ctx) {
        Term a = oneOf(ctx.specialTerm(), ctx.funcpredvarterm(),
                ctx.term(), ctx.boolean_constant(), ctx.ifExThenElseTerm(),
                ctx.ifThenElseTerm(), ctx.string_literal());
        if (ctx.LGUILLEMETS() != null) {
            ImmutableArray<TermLabel> labels = accept(ctx.label());
            if (labels.size() > 0) {
                a = getServices().getTermBuilder().addLabel(a, labels);
            }
        }
        return a;
    }

    @Override
    public ImmutableArray<TermLabel> visitLabel(KeYParser.LabelContext ctx) {
        List<TermLabel> labels = allOf(ctx.single_label());
        return new ImmutableArray(labels);
    }

    @Override
    public TermLabel visitSingle_label(KeYParser.Single_labelContext ctx) {
        String labelName = "";
        TermLabel left = null;
        TermLabel right = null;

        if (ctx.IDENT() != null)
            labelName = ctx.IDENT().getText();
        if (ctx.STAR() != null)
            labelName = ctx.STAR().getText();

        TermLabel label = null;
        List<String> parameters = allOf(ctx.string_value());
        try {
            if (inSchemaMode()) {
                SchemaVariable var = schemaVariables().lookup(
                        new Name(labelName));
                if (var instanceof TermLabel) {
                    label = (TermLabel) var;
                }
            }
            if (label == null) {
                label = getServices().getProfile()
                        .getTermLabelManager()
                        .parseLabel(labelName, parameters, getServices());
            }
        } catch (Exception ex) {
            throwEx(new KeYSemanticException(null, getSourceName(), ex));
        }
        return label;
    }

    @Override
    public Object visitAbbreviation(KeYParser.AbbreviationContext ctx) {
        String sc = accept(ctx.sc);
        Term a = scm.getTerm(sc);
        if (a == null) {
            throwEx(new NotDeclException(null, "abbreviation", sc));
        }
        return a;
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
        return getTermFactory().createTerm(IfThenElse.IF_THEN_ELSE, condF, thenT, elseT);
    }

    /**
     * Helper function for avoiding cast.
     *
     * @param ctx
     * @param <T>
     * @return
     */
    public <T> @Nullable T accept(@Nullable ParserRuleContext ctx) {
        if (ctx == null) {
            return null;
        }
        return (T) ctx.accept(this);
    }

    @Override
    public Object visitIfExThenElseTerm(KeYParser.IfExThenElseTermContext ctx) {
        Namespace<QuantifiableVariable> orig = variables();
        List<QuantifiableVariable> exVars = accept(ctx.bound_variables());
        Term condF = accept(ctx.condF);
        if (condF.sort() != Sort.FORMULA) {
            semanticError("Condition of an \\ifEx-then-else term has to be a formula.");
        }

        Term thenT = accept(ctx.thenT);
        Term elseT = accept(ctx.elseT);
        ImmutableArray<QuantifiableVariable> exVarsArray
                = new ImmutableArray<>(exVars);
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
        return (Term) oneOf(ctx.term(), ctx.term60());
    }

    @Override
    public Term visitQuantifierterm(KeYParser.QuantifiertermContext ctx) {
        Operator op = null;
        Namespace<QuantifiableVariable> orig = variables();
        if (ctx.FORALL() != null)
            op = Quantifier.ALL;
        if (ctx.EXISTS() != null)
            op = Quantifier.EX;
        List<QuantifiableVariable> vs = (List<QuantifiableVariable>) visit(ctx.bound_variables());
        Term a1 = accept(ctx.term60());
        var a = getTermFactory().createTerm(op,
                new ImmutableArray<Term>(a1),
                new ImmutableArray<>(vs.toArray(new QuantifiableVariable[0])),
                null);
        if (!isGlobalDeclTermParser())
            unbindVars(orig);
        return a;
    }

    @Override
    public Term visitBraces_term(KeYParser.Braces_termContext ctx) {
        return (Term) oneOf(ctx.substitutionterm(), ctx.locset_term(), ctx.updateterm());
    }

    @Override
    public Term visitLocset_term(KeYParser.Locset_termContext ctx) {
        List<Term> terms = mapOf(ctx.location_term());
        return getServices().getTermBuilder().union(terms);
    }

    @Override
    public Object visitLocation_term(KeYParser.Location_termContext ctx) {
        Term obj = accept(ctx.obj);
        Term field = accept(ctx.field);
        return getServices().getTermBuilder().singleton(obj, field);
    }

    @Override
    public Term visitSubstitutionterm(KeYParser.SubstitutiontermContext ctx) {
        SubstOp op = WarySubstOp.SUBST;
        Namespace<QuantifiableVariable> orig = variables();
        AbstractSortedOperator v = accept(ctx.v);
        if (!isGlobalDeclTermParser()) {
            unbindVars(orig);
            if (v instanceof LogicVariable)
                bindVar((LogicVariable) v);
            else
                bindVar();
        }

        Term a1 = accept(ctx.a1);
        Term a2 = accept(ctx.a2);
        Term result = getServices().getTermBuilder().subst(op, (QuantifiableVariable) v, a1, a2);
        if (!isGlobalDeclTermParser()) unbindVars(orig);
        return result;
    }

    @Override
    public Term visitUpdateterm(KeYParser.UpdatetermContext ctx) {
        Term u = accept(ctx.u);
        Term a2 = oneOf(ctx.term110(), ctx.unary_formula());
        return getTermFactory().createTerm(UpdateApplication.UPDATE_APPLICATION, u, a2);
    }

    public List<QuantifiableVariable> visitBound_variables(KeYParser.Bound_variablesContext ctx) {
        List<QuantifiableVariable> seq = ctx.one_bound_variable().stream()
                .map(it -> (QuantifiableVariable) it.accept(this))
                .collect(Collectors.toList());
        return seq;
    }

    @Override
    public QuantifiableVariable visitOne_bound_variable(KeYParser.One_bound_variableContext ctx) {
        return oneOf(ctx.one_logic_bound_variable_nosort(), ctx.one_schema_bound_variable(),
                ctx.one_logic_bound_variable());
    }

    @Override
    public Object visitOne_schema_bound_variable(KeYParser.One_schema_bound_variableContext ctx) {
        String id = accept(ctx.simple_ident());
        var ts = schemaVariables().lookup(new Name(id));
        if (!(ts instanceof VariableSV)) {
            semanticError(ts + " is not allowed in a quantifier. Note, that you can't "
                    + "use the normal syntax for quantifiers of the form \"\\exists int i;\""
                    + " in taclets. You have to define the variable as a schema variable"
                    + " and use the syntax \"\\exists i;\" instead.");
        }
        QuantifiableVariable v = (QuantifiableVariable) ts;
        bindVar();
        //TODO?
        return v;
    }

    @Override
    public Object visitOne_logic_bound_variable(KeYParser.One_logic_bound_variableContext ctx) {
        return bindVar(ctx.id.getText(), (Sort) ctx.s.accept(this));
    }

    @Override
    public LogicVariable visitOne_logic_bound_variable_nosort(KeYParser.One_logic_bound_variable_nosortContext ctx) {
        return (LogicVariable) variables().lookup(new Name(ctx.id.getText()));
    }

    @Override
    public Object visitModality_dl_term(KeYParser.Modality_dl_termContext ctx) {
        Term _modality_dl_term = null;
        Operator op = null;
        Term a = null;
        PairOfStringAndJavaBlock sjb = null; //TODO getJavaBlock(ctx.modality);
        //Debug.out("op: ", sjb.opName);
        //Debug.out("program: ", sjb.javaBlock);
        if (false && sjb.opName.charAt(0) == '#') {
            if (!inSchemaMode()) {
                semanticError("No schema elements allowed outside taclet declarations (" + sjb.opName + ")");
            }
            op = schemaVariables().lookup(new Name(sjb.opName));
        } else {
            op = Modality.getModality(sjb.opName);
        }
        if (op == null) {
            semanticError("Unknown modal operator: " + sjb.opName);
        }
        // CAREFUL here, op can be null during guessing stage (use lazy &&)
        //({op != null && op.arity() == 1} ?
        Term a1 = (Term) ctx.a1.accept(this);
        return getTermFactory().createTerm(op, new Term[]{a1}, null, sjb.javaBlock);
    }

    @Override
    public List<Term> visitArgument_list(KeYParser.Argument_listContext ctx) {
        return allOf(ctx.argument());
    }

    @Override
    public Object visitChar_literal(KeYParser.Char_literalContext ctx) {
        String s = ctx.CHAR_LITERAL().getText();
        int intVal = 0;
        if (s.length() == 3) {
            intVal = s.charAt(1);
        } else {
            try {
                intVal = Integer.parseInt(s.substring(3, s.length() - 1), 16);
            } catch (NumberFormatException ex) {
                semanticError("'" + s + "' is not a valid character.");
            }
        }
        return getTermFactory().createTerm(
                functions().lookup(new Name("C")),
                toZNotation("" + intVal, functions()).sub(0));
    }

    @Override
    public Term visitFuncpredvarterm(KeYParser.FuncpredvartermContext ctx) {
        Term _func_pred_var_term = null;
        String neg = "";
        boolean opSV = false;
        Namespace<QuantifiableVariable> orig = variables();
        boolean limited = false;

        if (ctx.char_literal() != null) return accept(ctx.char_literal());
        if (ctx.number() != null) return accept(ctx.number());
        if (ctx.AT() != null) return accept(ctx.abbreviation());

        String varfuncid = accept(ctx.funcpred_name());
        List<QuantifiableVariable> boundVars = accept(ctx.bound_variables());
        Term[] args = accept(ctx.argument_list());
        Term a = null;
        try {
            if (varfuncid.equals("skip") && args == null) {
                a = getTermFactory().createTerm(UpdateJunctor.SKIP);
            } else {
                Operator op;
                if (varfuncid.endsWith(LIMIT_SUFFIX)) {
                    varfuncid = varfuncid.substring(0, varfuncid.length() - 5);
                    op = lookupVarfuncId(varfuncid, args);
                    if (ObserverFunction.class.isAssignableFrom(op.getClass())) {
                        op = getServices().getSpecificationRepository()
                                .limitObs((ObserverFunction) op).first;
                    } else {
                        semanticError("Cannot can be limited: " + op);
                    }
                } else {
                    op = lookupVarfuncId(varfuncid, args);
                }

                if (op instanceof ParsableVariable) {
                    a = termForParsedVariable((ParsableVariable) op);
                } else {
                    if (args == null) {
                        args = new Term[0];
                    }

                    if (boundVars == null) {
                        a = getTermFactory().createTerm(op, args);
                    } else {
                        //sanity check
                        assert op instanceof Function;
                        for (int i = 0; i < args.length; i++) {
                            if (i < op.arity() && !op.bindVarsAt(i)) {
                                for (QuantifiableVariable qv : args[i].freeVars()) {
                                    if (boundVars.contains(qv)) {
                                        semanticError("Building function term " + op + " with bound variables failed: "
                                                + "Variable " + qv + " must not occur free in subterm " + args[i]);
                                    }
                                }
                            }
                        }

                        //create term
                        a = getTermFactory().createTerm(op, args, new ImmutableArray<QuantifiableVariable>(boundVars.toArray(new QuantifiableVariable[boundVars.size()])), null);
                    }
                }
            }
        } catch (Exception e) {
            throwEx(e);
        }
        if (boundVars != null) {
            unbindVars(orig);
        }
        return a;
    }

    @Override
    public Object visitNumber(KeYParser.NumberContext ctx) {
        return toZNotation(ctx.getText(), functions());
    }

    @Override
    public Term visitSpecialTerm(KeYParser.SpecialTermContext ctx) {
        return (Term) ctx.result.accept(this);
    }

    @Override
    public String visitArith_op(KeYParser.Arith_opContext ctx) {
        /*    PERCENT {op = "\%";}
  | STAR {op = "*";}
  | MINUS {op = "-";}
  | SLASH {op = "/";}
  | PLUS { op = "+";}*/
        return ctx.getText();
    }

    @Override
    public Object visitVarId(KeYParser.VarIdContext ctx) {
        var id = ctx.id.getText();
        var v = variables().lookup(new Name(ctx.id.getText()));
        if (v == null) {
            return schemaVariables().lookup(new Name(id));
        }
        if (v == null) {
            throwEx(new NotDeclException(null, "variable", id));
        }
        return v;
    }

    @Override
    public Object visitVarIds(KeYParser.VarIdsContext ctx) {
        Collection<String> ids = (Collection<String>) ctx.simple_ident_comma_list().accept(this);
        List<ParsableVariable> list = new ArrayList<>(ids.size());
        for (String id : ids) {
            var v = (ParsableVariable) variables().lookup(new Name(id));
            if (v == null) {
                v = schemaVariables().lookup(new Name(id));
            }
            if (v == null) {
                semanticError("Variable " + id + " not declared.");
            }
            list.add(v);
        }
        return list;
    }

    @Override
    public TacletBuilder visitTriggers(KeYParser.TriggersContext ctx) {
        String id = (String) ctx.id.accept(this);
        SchemaVariable triggerVar = schemaVariables().lookup(new Name(id));
        if (triggerVar == null) {
            semanticError("Undeclared schemavariable: " + id);
        }
        Term t = accept(ctx.t);
        List<Term> avoidConditions = new ArrayList<>(ctx.term().size());//TODO avoidCond.
        //b.setTrigger(new Trigger(triggerVar, t, avoidConditions));
        return null;
    }

    @Override
    public Taclet visitTaclet(KeYParser.TacletContext ctx) {
        var ifSeq = Sequent.EMPTY_SEQUENT;
        b = null;
        int applicationRestriction = RewriteTaclet.NONE;

        switchToNormalMode();
        ImmutableSet<TacletAnnotation> tacletAnnotations = DefaultImmutableSet.nil();

        if (ctx.LEMMA() != null) {
            tacletAnnotations = tacletAnnotations.add(de.uka.ilkd.key.rule.TacletAnnotation.LEMMA);
        }
        var name = ctx.name.getText();
        ImmutableSet<Choice> choices_ =
                DefaultImmutableSet.fromSet(accept(ctx.option_list()));

        Term form = accept(ctx.form);
        if (form != null) {
            if (!axiomMode) {
                semanticError("formula rules are only permitted for \\axioms");
            }
            b = createTacletBuilderFor(null, RewriteTaclet.NONE);
            SequentFormula sform = new SequentFormula(form);
            Semisequent semi = new Semisequent(sform);
            Sequent addSeq = Sequent.createAnteSequent(semi);
            ImmutableList<Taclet> noTaclets = ImmutableSLList.nil();
            DefaultImmutableSet<SchemaVariable> noSV = DefaultImmutableSet.nil();
            addGoalTemplate(b, null, null, addSeq, noTaclets, noSV, null);
            b.setName(new Name(name));
            b.setChoices(choices_);
            b.setAnnotations(tacletAnnotations);
            Taclet r = b.getTaclet();
            taclet2Builder.put(r, b);
            return r;
        }

        switchToSchemaMode();
        //  schema var decls
        schemaVariablesNamespace = new Namespace(schemaVariables());
        allOf(ctx.one_schema_var_decl());
        accept(ctx.ifSeq);

        if (null != ctx.SAMEUPDATELEVEL()) {
            applicationRestriction |= RewriteTaclet.SAME_UPDATE_LEVEL;
        }
        if (null != ctx.INSEQUENTSTATE()) {
            applicationRestriction |= RewriteTaclet.IN_SEQUENT_STATE;
        }
        if (null != ctx.ANTECEDENTPOLARITY()) {
            applicationRestriction |= RewriteTaclet.ANTECEDENT_POLARITY;
        }
        if (null != ctx.SUCCEDENTPOLARITY()) {
            applicationRestriction |= RewriteTaclet.SUCCEDENT_POLARITY;
        }
        var find = accept(ctx.find);
        b = createTacletBuilderFor(find, applicationRestriction);
        b.setIfSequent(accept(ctx.ifSeq));
        b.setName(new Name(name));
        accept(ctx.varexplist());
        accept(ctx.goalspecs());
        accept(ctx.modifiers());
        b.setChoices(choices_);
        b.setAnnotations(tacletAnnotations);
        Taclet r = b.getTaclet();
        taclet2Builder.put(r, b);
        // dump local schema var decls
        schemaVariablesNamespace = schemaVariables().parent();
        return r;
    }

    @Override
    public Object visitModifiers(KeYParser.ModifiersContext ctx) {
        if (ctx.rs != null) {
            List<RuleSet> it = accept(ctx.rs);
            it.forEach(a -> b.addRuleSet(a));
        }

        if (ctx.NONINTERACTIVE() != null) {
            b.addRuleSet(ruleSets().lookup(new Name("notHumanReadable")));
        }

        if (ctx.DISPLAYNAME() != null) {
            b.setDisplayName(accept(ctx.dname));
        }

        if (ctx.HELPTEXT() != null) {
            b.setHelpText(accept(ctx.htext));
        }

        allOf(ctx.triggers());
        return null;
    }

    @Override
    public Sequent visitSeq(KeYParser.SeqContext ctx) {
        Semisequent ant = accept(ctx.ant);
        Semisequent suc = accept(ctx.suc);
        return Sequent.createSequent(ant, suc);
    }

    @Override
    public Object visitSeqEOF(KeYParser.SeqEOFContext ctx) {
        return accept(ctx.seq());
    }

    @Override
    public Object visitTermorseq(KeYParser.TermorseqContext ctx) {
        Term head = accept(ctx.head);
        Sequent s = accept(ctx.s);
        Semisequent ss = accept(ctx.ss);
        if (head != null && s == null && ss == null) {
            return head;
        }
        if (head != null && ss != null) {
            // A sequent with only head in the antecedent.
            Semisequent ant = Semisequent.EMPTY_SEMISEQUENT;
            ant = ant.insertFirst(
                    new SequentFormula(head)).semisequent();
            return Sequent.createSequent(ant, ss);
        }
        if (head != null && s != null) {
            // A sequent.  Prepend head to the antecedent.
            Semisequent newAnt = s.antecedent();
            newAnt = newAnt.insertFirst(
                    new SequentFormula(head)).semisequent();
            return Sequent.createSequent(newAnt, s.succedent());
        }
        if (ss != null) {
            return Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT, ss);
        }
        assert (false);
        return null;
    }

    @Override
    public Object visitSemisequent(KeYParser.SemisequentContext ctx) {
        Semisequent ss = accept(ctx.ss);
        if (ss == null)
            ss = Semisequent.EMPTY_SEMISEQUENT;
        Term head = accept(ctx.term());
        if (head != null)
            ss = ss.insertFirst(new SequentFormula(head)).semisequent();
        return ss;
    }

    @Override
    public Object visitVarexplist(KeYParser.VarexplistContext ctx) {
        return allOf(ctx.varexp());
    }

    @Override
    public Object visitVarexp(KeYParser.VarexpContext ctx) {
        negated = ctx.NOT_() != null;
        return super.visitVarexp(ctx);
        /*ctx.varcond_applyUpdateOnRigid()
                , ctx.varcond_dropEffectlessElementaries()
                , ctx.varcond_dropEffectlessStores()
                , ctx.varcond_enum_const()
                , ctx.varcond_free()
                , ctx.varcond_hassort()
                , ctx.varcond_fieldtype()
                , ctx.varcond_equalUnique()
                , ctx.varcond_new()
                , ctx.varcond_newlabel()
                , ctx.varcond_observer()
                , ctx.varcond_different()
                , ctx.varcond_metadisjoint()
                , ctx.varcond_simplifyIfThenElseUpdate()
                , ctx.varcond_differentFields()
                , ctx.varcond_sameObserver()
                , ctx.varcond_abstractOrInterface()
                , ctx.varcond_array()
                , ctx.varcond_array_length()
                , ctx.varcond_enumtype()
                , ctx.varcond_freeLabelIn()
                , ctx.varcond_localvariable()
                , ctx.varcond_thisreference()
                , ctx.varcond_reference()
                , ctx.varcond_referencearray()
                , ctx.varcond_static()
                , ctx.varcond_staticmethod()
                , ctx.varcond_mayexpandmethod()
                , ctx.varcond_final()
                , ctx.varcond_typecheck()
                , ctx.varcond_constant()
                , ctx.varcond_label()
                , ctx.varcond_static_field()
                , ctx.varcond_subFormulas()
                , ctx.varcond_containsAssignment());
    */
    }

    @Override
    public Object visitVarcond_sameObserver(KeYParser.Varcond_sameObserverContext ctx) {
        ParsableVariable t1 = accept(ctx.t1);
        ParsableVariable t2 = accept(ctx.t2);
        b.addVariableCondition(new SameObserverCondition(t1, t2));
        return null;
    }

    @Override
    public Object visitVarcond_applyUpdateOnRigid(KeYParser.Varcond_applyUpdateOnRigidContext ctx) {
        var u = accept(ctx.u);
        var x = accept(ctx.x);
        var x2 = accept(ctx.x2);
        b.addVariableCondition(new ApplyUpdateOnRigidCondition((UpdateSV) u,
                (SchemaVariable) x,
                (SchemaVariable) x2));
        return null;
    }

    @Override
    public Object visitVarcond_dropEffectlessElementaries(KeYParser.Varcond_dropEffectlessElementariesContext ctx) {
        UpdateSV u = accept(ctx.u);
        SchemaVariable x = accept(ctx.x);
        SchemaVariable result = accept(ctx.result);
        b.addVariableCondition(new DropEffectlessElementariesCondition(
                u, x, result));
        return null;
    }

    @Override
    public Object visitVarcond_dropEffectlessStores(KeYParser.Varcond_dropEffectlessStoresContext ctx) {
        var h = accept(ctx.h);
        var o = accept(ctx.o);
        var f = accept(ctx.f);
        var x = accept(ctx.x);
        var result = accept(ctx.result);
        b.addVariableCondition(new DropEffectlessStoresCondition((TermSV) h,
                (TermSV) o,
                (TermSV) f,
                (TermSV) x,
                (TermSV) result));
        return null;
    }

    @Override
    public Object visitVarcond_differentFields(KeYParser.Varcond_differentFieldsContext ctx) {
        var x = accept(ctx.x);
        var y = accept(ctx.y);
        b.addVariableCondition(new DifferentFields((SchemaVariable) x, (SchemaVariable) y));
        return null;
    }

    @Override
    public Object visitVarcond_simplifyIfThenElseUpdate(KeYParser.Varcond_simplifyIfThenElseUpdateContext ctx) {
        FormulaSV phi = accept(ctx.phi);
        UpdateSV u1 = accept(ctx.u1);
        UpdateSV u2 = accept(ctx.u2);
        FormulaSV commonFormula = accept(ctx.commonFormula);
        SchemaVariable result = accept(ctx.result);
        b.addVariableCondition(new SimplifyIfThenElseUpdateCondition(phi,
                u1,
                u2,
                commonFormula,
                result));
        return null;
    }

    @Override
    public Object visitType_resolver(KeYParser.Type_resolverContext ctx) {
        Sort s = accept(ctx.any_sortId_check());
        var y = accept(ctx.y);
        if (s != null) {
            if (s instanceof GenericSort) {
                return TypeResolver.createGenericSortResolver((GenericSort) s);
            } else {
                return TypeResolver.createNonGenericSortResolver(s);
            }
        }
        if (ctx.TYPEOF() != null) {
            return TypeResolver.createElementTypeResolver((SchemaVariable) y);
        }
        if (ctx.CONTAINERTYPE() != null) {
            return TypeResolver.createContainerTypeResolver((SchemaVariable) y);
        }
        return null;
    }

    @Override
    public Object visitVarcond_new(KeYParser.Varcond_newContext ctx) {
        var x = accept(ctx.x);
        var y = accept(ctx.y);
        if (ctx.TYPEOF() != null) {
            b.addVarsNew((SchemaVariable) x, (SchemaVariable) y);
        }

        if (ctx.DEPENDINGON() != null) {
            b.addVarsNewDependingOn((SchemaVariable) x, (SchemaVariable) y);
        }

        if (ctx.kjt != null) {
            KeYJavaType kjt = accept(ctx.kjt);
            b.addVarsNew((SchemaVariable) x, kjt.getJavaType());
        }
        return null;
    }

    @Override
    public Object visitVarcond_newlabel(KeYParser.Varcond_newlabelContext ctx) {
        var x = accept(ctx.x);
        b.addVariableCondition(new NewJumpLabelCondition((SchemaVariable) x));
        return null;
    }

    @Override
    public Object visitVarcond_typecheck(KeYParser.Varcond_typecheckContext ctx) {
        TypeComparisonCondition.Mode mode = null;
        if (ctx.SAME() != null) {
            mode = negated
                    ? TypeComparisonCondition.Mode.NOT_SAME
                    : TypeComparisonCondition.Mode.SAME;
        }
        if (ctx.ISSUBTYPE() != null) {
            mode = negated
                    ? TypeComparisonCondition.Mode.NOT_IS_SUBTYPE
                    : TypeComparisonCondition.Mode.IS_SUBTYPE;
        }
        if (ctx.STRICT() != null) {
            if (negated)
                semanticError("A negated strict subtype check does not make sense.");
            mode = TypeComparisonCondition.Mode.STRICT_SUBTYPE;
        }
        if (ctx.DISJOINTMODULONULL() != null) {
            if (negated)
                semanticError("Negation not supported");
            mode = TypeComparisonCondition.Mode.DISJOINTMODULONULL;
        }

        TypeResolver fst = accept(ctx.fst);
        TypeResolver snd = accept(ctx.snd);
        b.addVariableCondition(new TypeComparisonCondition(fst, snd, mode));
        return null;
    }

    @Override
    public Object visitVarcond_free(KeYParser.Varcond_freeContext ctx) {
        SchemaVariable x = accept(ctx.x);
        List<SchemaVariable> ys = accept(ctx.varIds());
        ys.forEach(it -> b.addVarsNotFreeIn(x, it));
        return null;
    }

    @Override
    public Object visitVarcond_hassort(KeYParser.Varcond_hassortContext ctx) {
        var x = accept(ctx.x);
        var elemSort = ctx.ELEMSORT() != null;
        Sort s = accept(ctx.any_sortId_check());
        if (!(s instanceof GenericSort)) {
            throwEx(new GenericSortException("sort",
                    "Generic sort expected",
                    s,
                    getSourceName(),
                    getLine(),
                    getColumn()));
        } else if (!JavaTypeToSortCondition.checkSortedSV((SchemaVariable) x)) {
            semanticError("Expected schema variable of kind EXPRESSION or TYPE, "
                    + "but is " + x);
        } else {
            b.addVariableCondition(new JavaTypeToSortCondition((SchemaVariable) x,
                    (GenericSort) s,
                    elemSort));
        }
        return null;
    }

    @Override
    public Object visitVarcond_fieldtype(KeYParser.Varcond_fieldtypeContext ctx) {
        var x = accept(ctx.x);
        Sort s = accept(ctx.any_sortId_check());

        if (!(s instanceof GenericSort)) {
            throwEx(new GenericSortException("sort",
                    "Generic sort expected",
                    s,
                    getSourceName(),
                    getLine(),
                    getColumn()));
        } else if (!FieldTypeToSortCondition.checkSortedSV((SchemaVariable) x)) {
            semanticError("Expected schema variable of kind EXPRESSION or TYPE, "
                    + "but is " + x);
        } else {
            b.addVariableCondition(new FieldTypeToSortCondition((SchemaVariable) x,
                    (GenericSort) s));
        }
        return null;
    }

    @Override
    public Object visitVarcond_containsAssignment(KeYParser.Varcond_containsAssignmentContext ctx) {
        var x = accept(ctx.x);
        b.addVariableCondition(new ContainsAssignmentCondition((SchemaVariable) x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_enumtype(KeYParser.Varcond_enumtypeContext ctx) {
        TypeResolver tr = accept(ctx.tr);
        b.addVariableCondition(new EnumTypeCondition(tr, negated));
        return null;
    }

    @Override
    public Object visitVarcond_reference(KeYParser.Varcond_referenceContext ctx) {
        boolean nonNull = false;
        String id = accept(ctx.id);
        if ("non_null" .equals(id)) {
            nonNull = true;
        } else {
            semanticError(id +
                    " is not an allowed modifier for the \\isReference variable condition.");
        }
        TypeResolver tr = accept(ctx.tr);
        b.addVariableCondition(new TypeCondition(tr, !isPrimitive, nonNull));
        return null;
    }

    @Override
    public Object visitVarcond_thisreference(KeYParser.Varcond_thisreferenceContext ctx) {
        String id = null;
        boolean nonNull = false;
        ParsableVariable x = accept(ctx.x);
        b.addVariableCondition(new IsThisReference(x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_staticmethod(KeYParser.Varcond_staticmethodContext ctx) {
        var x = accept(ctx.x);
        var y = accept(ctx.y);
        var z = accept(ctx.z);
        b.addVariableCondition(new StaticMethodCondition
                (negated, (SchemaVariable) x, (SchemaVariable) y, (SchemaVariable) z));
        return null;
    }

    @Override
    public Object visitVarcond_mayexpandmethod(KeYParser.Varcond_mayexpandmethodContext ctx) {
        SchemaVariable x = accept(ctx.x);
        SchemaVariable y = accept(ctx.y);
        SchemaVariable z = accept(ctx.z);
        if (z != null)
            b.addVariableCondition(new MayExpandMethodCondition(
                    negated, x, y, z));
        else
            b.addVariableCondition(new MayExpandMethodCondition(
                    negated, null, x, y));
        return null;
    }

    @Override
    public Object visitVarcond_referencearray(KeYParser.Varcond_referencearrayContext ctx) {
        SchemaVariable x = accept(ctx.x);
        b.addVariableCondition(new ArrayComponentTypeCondition(
                x, !primitiveElementType));
        return null;
    }

    @Override
    public Object visitVarcond_array(KeYParser.Varcond_arrayContext ctx) {
        SchemaVariable x = accept(ctx.x);
        b.addVariableCondition(new ArrayTypeCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_array_length(KeYParser.Varcond_array_lengthContext ctx) {
        SchemaVariable x = accept(ctx.x);
        b.addVariableCondition(new ArrayLengthCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_abstractOrInterface(KeYParser.Varcond_abstractOrInterfaceContext ctx) {
        TypeResolver tr = accept(ctx.tr);
        b.addVariableCondition(new AbstractOrInterfaceType(tr, negated));
        return null;
    }

    @Override
    public Object visitVarcond_enum_const(KeYParser.Varcond_enum_constContext ctx) {
        SchemaVariable x = accept(ctx.x);
        b.addVariableCondition(new EnumConstantCondition(
                x));
        return null;
    }

    @Override
    public Object visitVarcond_final(KeYParser.Varcond_finalContext ctx) {
        SchemaVariable x = accept(ctx.x);
        b.addVariableCondition(new FinalReferenceCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_static(KeYParser.Varcond_staticContext ctx) {
        SchemaVariable x = accept(ctx.x);
        b.addVariableCondition(new StaticReferenceCondition(
                x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_localvariable(KeYParser.Varcond_localvariableContext ctx) {
        SchemaVariable x = accept(ctx.x);
        b.addVariableCondition(new LocalVariableCondition(x, negated));
        return null;
    }

    @Override
    public Object visitVarcond_observer(KeYParser.Varcond_observerContext ctx) {
        TermSV obs = accept(ctx.obs);
        TermSV heap = accept(ctx.heap);

        b.addVariableCondition(new ObserverCondition(obs,
                heap));
        return null;
    }

    @Override
    public Object visitVarcond_different(KeYParser.Varcond_differentContext ctx) {
        SchemaVariable var1 = accept(ctx.var1);
        SchemaVariable var2 = accept(ctx.var2);
        b.addVariableCondition(new DifferentInstantiationCondition(
                var1,
                var2));
        return null;
    }

    @Override
    public Object visitVarcond_metadisjoint(KeYParser.Varcond_metadisjointContext ctx) {
        var var1 = accept(ctx.var1);
        var var2 = accept(ctx.var2);
        b.addVariableCondition(new MetaDisjointCondition(
                (TermSV) var1,
                (TermSV) var2));
        return null;
    }

    @Override
    public Object visitVarcond_equalUnique(KeYParser.Varcond_equalUniqueContext ctx) {
        var t = accept(ctx.t);
        var t2 = accept(ctx.t2);
        var phi = accept(ctx.phi);
        b.addVariableCondition(new EqualUniqueCondition((TermSV) t,
                (TermSV) t2,
                (FormulaSV) phi));
        return null;
    }

    @Override
    public Object visitVarcond_freeLabelIn(KeYParser.Varcond_freeLabelInContext ctx) {
        var l = accept(ctx.l);
        var statement = accept(ctx.statement);
        b.addVariableCondition(new FreeLabelInVariableCondition((SchemaVariable) l,
                (SchemaVariable) statement, negated));
        return null;
    }

    @Override
    public Object visitVarcond_constant(KeYParser.Varcond_constantContext ctx) {
        var x = accept(ctx.varId());
        if (x instanceof TermSV) {
            b.addVariableCondition(new ConstantCondition((TermSV) x, negated));
        } else {
            assert x instanceof FormulaSV;
            b.addVariableCondition(new ConstantCondition((FormulaSV) x, negated));
        }
        return null;
    }

    @Override
    public Object visitVarcond_label(KeYParser.Varcond_labelContext ctx) {
        TermLabelSV l = accept(ctx.varId());
        String name = accept(ctx.simple_ident());
        b.addVariableCondition(new TermLabelCondition(l, name, negated));
        return null;
    }

    @Override
    public Object visitVarcond_static_field(KeYParser.Varcond_static_fieldContext ctx) {
        var field = accept(ctx.varId());
        b.addVariableCondition(new StaticFieldCondition((SchemaVariable) field, negated));
        return null;
    }

    @Override
    public Object visitVarcond_subFormulas(KeYParser.Varcond_subFormulasContext ctx) {
        FormulaSV x = accept(ctx.varId());
        b.addVariableCondition(new SubFormulaCondition(x, negated));
        return null;
    }

    @Override
    public Object visitGoalspecs(KeYParser.GoalspecsContext ctx) {
        return allOf(ctx.goalspecwithoption());
    }

    @Override
    public Object visitGoalspecwithoption(KeYParser.GoalspecwithoptionContext ctx) {
        //TODO
        var soc = accept(ctx.option_list());
        accept(ctx.goalspec());
        return null;
    }

    @Override
    public Object visitOption(KeYParser.OptionContext ctx) {
        String cat = ctx.cat.toString();
        String name = ctx.choice_.toString();
        var c = choices().lookup(new Name(cat + ":" + name));
        if (c == null) {
            throwEx(new NotDeclException(null, "Option", name));
        }
        return c;
    }

    @Override
    public List<Choice> visitOption_list(KeYParser.Option_listContext ctx) {
        return allOf(ctx.option());
    }

    @Override
    public Object visitGoalspec(KeYParser.GoalspecContext ctx) {
        ImmutableSet<Choice> soc = null;
        boolean ruleWithFind;
        var addSeq = Sequent.EMPTY_SEQUENT;
        var addRList = ImmutableSLList.<Taclet>nil();
        var addpv = DefaultImmutableSet.<SchemaVariable>nil();

        String name = accept(ctx.string_value());

        var rwObj = accept(ctx.replacewith());
        addSeq = accept(ctx.add());
        addRList = accept(ctx.addrules());
        addpv = accept(ctx.addprogvar());
        addGoalTemplate(b, name, rwObj, addSeq, addRList, addpv, soc);
        return null;
    }

    @Override
    public Object visitReplacewith(KeYParser.ReplacewithContext ctx) {
        return accept(ctx.o);
    }

    @Override
    public Object visitAdd(KeYParser.AddContext ctx) {
        return accept(ctx.s);
    }

    @Override
    public Object visitAddrules(KeYParser.AddrulesContext ctx) {
        return accept(ctx.lor);
    }

    @Override
    public ImmutableSet<SchemaVariable> visitAddprogvar(KeYParser.AddprogvarContext ctx) {
        return accept(ctx.pvs);
    }

    @Override
    public List<Taclet> visitTacletlist(KeYParser.TacletlistContext ctx) {
        return allOf(ctx.taclet());
    }

    @Override
    public List<String> visitPvset(KeYParser.PvsetContext ctx) {
        return allOf(ctx.varId());
    }

    @Override
    public List<RuleSet> visitRulesets(KeYParser.RulesetsContext ctx) {
        return mapOf(ctx.ruleset());
    }

    @Override
    public Object visitRuleset(KeYParser.RulesetContext ctx) {
        String id = (String) ctx.IDENT().accept(this);
        RuleSet h = ruleSets().lookup(new Name(id));
        if (h == null) {
            throwEx(new NotDeclException(null, "ruleset", id));
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
    public Term visitMetaTerm(KeYParser.MetaTermContext ctx) {
        Operator metaId = accept(ctx.metaId());
        List<Term> t = allOf(ctx.term());
        return getTermFactory().createTerm(metaId, t);
    }

    @Override
    public Object visitContracts(KeYParser.ContractsContext ctx) {
        switchToNormalMode();
        return allOf(ctx.one_contract());
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
    public Term visitProblem(KeYParser.ProblemContext ctx) {
        boolean axiomMode = false;
        int beginPos = 0;
        DefaultImmutableSet<Choice> choices
                = DefaultImmutableSet.nil();
        chooseContract = this.chooseContract;
        proofObligation = this.proofObligation;

        var profile = accept(ctx.profile());
        var pref = accept(ctx.preferences());
        String bootClassPath = accept(ctx.bootClassPath());
        String classPath = accept(ctx.classPaths());
        String javaSource = accept(ctx.javaSource());

        allOf(ctx.contracts());
        allOf(ctx.invariants());

        if (ctx.RULES() != null)
            axiomMode = false;
        if (ctx.AXIOMS() != null)
            axiomMode = true;

        List<Choice> seqChoices = allOf(ctx.option_list());

        List<Taclet> seq = allOf(ctx.taclet());
        Map<RuleKey, Taclet> taclets = new HashMap<>();
        if (!skip_taclets) {
            for (Taclet s : seq) {
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
        choices = DefaultImmutableSet.nil();

        Term a = null;
        if (ctx.PROBLEM() != null) {
            switchToNormalMode();
            a = accept(ctx.formula());
        }

        chooseContract = "";
        if (ctx.CHOOSECONTRACT() != null)
            chooseContract = accept(ctx.chooseContract);

        proofObligation = "";
        if (ctx.PROOFOBLIGATION() != null)
            proofObligation = accept(ctx.proofObligation);
        return a;
    }

    @Override
    public String visitBootClassPath(KeYParser.BootClassPathContext ctx) {
        return accept(ctx.string_value());
    }

    @Override
    public String visitClassPaths(KeYParser.ClassPathsContext ctx) {
        if (ctx.NODEFAULTCLASSES() != null) {
            throwEx(new NoViableAltException(
                    "\\noDefaultClasses is no longer supported. " +
                            "Use \\bootclasspath. See docs/README.classpath", -1, -1, null));
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
        profileName = (String) visit(ctx.name);
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
        return new Triple<>(content, line, col);
    }

    @Override
    public String visitString_value(KeYParser.String_valueContext ctx) {
        return ctx.getText().substring(1, ctx.getText().length() - 1);
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
    private static class PairOfStringAndJavaBlock {
        String opName;
        JavaBlock javaBlock;
    }
}
