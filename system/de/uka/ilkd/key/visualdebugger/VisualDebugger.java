package de.uka.ilkd.key.visualdebugger;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ArrayOfParameterDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.ArrayOfProgramPrefix;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.IteratorOfConstrainedFormula;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SetAsListOfTerm;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.AttributeOp;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IteratorOfProgramMethod;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.ListOfProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuanUpdateOperator;
import de.uka.ilkd.key.logic.op.SLListOfProgramVariable;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IteratorOfGoal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.ListOfRuleSet;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.DebuggerStrategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.key.visualdebugger.executiontree.ExecutionTree;
import de.uka.ilkd.key.visualdebugger.executiontree.ITNode;
import de.uka.ilkd.key.visualdebugger.statevisualisation.StateVisualization;
import de.uka.ilkd.key.visualdebugger.statevisualisation.SymbolicObject;

// TODO: Auto-generated Javadoc
/**
 * The Class VisualDebugger.
 */
public class VisualDebugger {

    /** The Constant debugClass. */
    public static final String debugClass = "Debug";

    /** The debugging mode. */
    private static boolean debuggingMode = false;

    /** The Constant debugPackage. */
    public static final String debugPackage = "visualdebugger";

    /** The key bugger mode. */
    static boolean keyBuggerMode;

    /** The quan_splitting. */
    public static boolean quan_splitting = false;

    /** The Constant sepName. */
    public static final String sepName = "sep";

    /** The show implicite attr. */
    public static boolean showImpliciteAttr = false;

    /** The show main window. */
    public static boolean showMainWindow = false;

    /** The VisualDebugger implements the singleton pattern. */
    private static VisualDebugger visualDebuggerInstance;

    /** The symbolic exec names. */
    private static List symbolicExecNames = new ArrayList(5);

    /** The ExecutionTreeView's progress monitor. */
    private ProgressMonitor etProgressMonitor = null;

    private WatchPointManager watchPointManager = null;

    /**
     * The Constant tempDir. A temporary directory in the users home:
     * ~/tmp/visualdebugger.
     */
    public static final String tempDir = System.getProperty("user.home")
            + File.separator + "tmp" + File.separator + "visualdebugger"
            + File.separator;

    /** The Constant vdInDebugMode. */
    public static final boolean vdInDebugMode = false;

    /** The Constant POST_PREDICATE_NAME. */
    private static final Name POST_PREDICATE_NAME = new Name("POST");

    static {
        symbolicExecNames.add(new Name("simplify_prog"));
        symbolicExecNames.add(new Name("simplify_autoname"));
        symbolicExecNames.add(new Name("simplify_int"));
        symbolicExecNames.add(new Name("simplify_object_creation"));
        symbolicExecNames.add(new Name("method_expand"));
    }

    /**
     * Contains implicit attr.
     * 
     * @param t
     *                the t
     * 
     * @return true, if successful
     */
    public static boolean containsImplicitAttr(Term t) {
        if (t.op() instanceof AttributeOp
                && ((ProgramVariable) ((AttributeOp) t.op()).attribute())
                        .isImplicit() || t.op() instanceof ProgramVariable
                && ((ProgramVariable) t.op()).isImplicit()) {
            return true;
        }
        for (int i = 0; i < t.arity(); i++) {
            if (containsImplicitAttr(t.sub(i))) {
                return true;
            }
        }
        return false;
    }

    /**
     * Gets the method string.
     * 
     * @param md
     *                the md
     * 
     * @return the method string
     */
    public static String getMethodString(MethodDeclaration md) {
        String result = md.getProgramElementName().toString() + "( ";
        final ArrayOfParameterDeclaration paraDecl = md.getParameters();
        if (paraDecl.size() > 0) {
            for (int i = 0; i < paraDecl.size() - 1; i++) {
                result += paraDecl.getParameterDeclaration(i) + " ,";
            }
            result += paraDecl.getParameterDeclaration(paraDecl.size() - 1);
        }
        result += " )";
        return result;

    }

    /**
     * Gets the visual debugger.
     *  Uses the singleton pattern.
     * @return the visual debugger
     */
    public static VisualDebugger getVisualDebugger() {
        if (visualDebuggerInstance == null) {
            visualDebuggerInstance = new VisualDebugger();
            String[] args = new String[2];

            args[0] = "DEBUGGER";
            args[1] = "LOOP";

            Main.evaluateOptions(args);
            Main key = Main.getInstance(false);
            key.loadCommandLineFile();

            visualDebuggerInstance.main = Main.getInstance(false);
            visualDebuggerInstance.mediator = visualDebuggerInstance.main.mediator();
            
        }
        return visualDebuggerInstance;
    }

    /**
     * Checks if is debugging mode.
     * 
     * @return true, if is debugging mode
     */
    public static boolean isDebuggingMode() {
        return debuggingMode;
    }

    /**
     * Prints the.
     * 
     * @param o
     *                the o
     */
    public static void print(Object o) {
        if (vdInDebugMode)
            System.out.println(o.toString());
    }

    /**
     * Prints the.
     * 
     * @param s
     *                the s
     */
    public static void print(String s) {
        if (vdInDebugMode)
            System.out.println(s);
    }

    /**
     * Sets the debugging mode.
     * 
     * @param mode
     *                the new debugging mode
     */
    public static void setDebuggingMode(boolean mode) {
        debuggingMode = mode;
    }

    /** The bp manager. */
    private BreakpointManager bpManager;

    /** The current state. */
    private StateVisualization currentState;

    /** The current tree. */
    private ITNode currentTree;

    /** The debugging method. */
    private ProgramMethod debuggingMethod;

    /** The init phase. */
    private boolean initPhase = false;

    /** The input p v2term. */
    private HashMap inputPV2term = new HashMap();

    /** The listeners. */
    private LinkedList listeners = new LinkedList();

    /** The main. */
    private Main main;

    /** The max proof steps for state vis computation. */
    protected int maxProofStepsForStateVisComputation = 8000;

    // InteractiveProver ip;
    /** The mediator. */
    private KeYMediator mediator;

    /** The precondition. */
    private Sequent precondition;

    /** The run limit. */
    private int runLimit = 5;

    /** The self pv. */
    private ProgramVariable selfPV;

    /** The static method. */
    private boolean staticMethod;

    /** The symbolic input values as list. */
    private ListOfTerm symbolicInputValuesAsList = SLListOfTerm.EMPTY_LIST;

    /** The tc2node. */
    private HashMap tc2node = new HashMap();

    /** The term2 input pv. */
    private HashMap term2InputPV = new HashMap();

    /** The type. */
    private ClassType type;

    /** The use decision procedures. */
    private boolean useDecisionProcedures = false;

    /** The post predicate. */
    private Function postPredicate;

    /**
     * Instantiates a new visual debugger.
     */
    protected VisualDebugger() {
        bpManager = new BreakpointManager(this);
        watchPointManager = new WatchPointManager();
        // main = Main.getInstance();
    }

    /**
     * Adds the listener.
     * 
     * @param listener
     *                the listener
     */
    public void addListener(DebuggerListener listener) {
        listeners.add(listener);
    }

    /**
     * Adds the test case.
     * 
     * @param file
     *                the file
     * @param method
     *                the method
     * @param n
     *                the n
     */
    public void addTestCase(String file, String method, Node n) {
        tc2node.put(new TestCaseIdentifier(file, method), n);

    }

    /**
     * Array of expression2 list of prog var.
     * 
     * @param aoe
     *                the aoe
     * @param start
     *                the start
     * 
     * @return the list of program variable
     */
    public ListOfProgramVariable arrayOfExpression2ListOfProgVar(
            ArrayOfExpression aoe, int start) {
        ListOfProgramVariable lopv = SLListOfProgramVariable.EMPTY_LIST;
        for (int i = start; i < aoe.size(); i++) {
            lopv = lopv.append((ProgramVariable) aoe.getExpression(i));
        }
        return lopv;
    }

    /**
     * Collect result.
     * 
     * @param s
     *                the s
     * 
     * @return the list of term
     */
    private ListOfTerm collectResult(Sequent s) {
        IteratorOfConstrainedFormula itc = s.antecedent().iterator();
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;
        while (itc.hasNext()) {
            result = result.append(itc.next().formula());
        }
        itc = s.succedent().iterator();
        while (itc.hasNext()) {
            result = result.append(TermFactory.DEFAULT.createJunctorTerm(
                    Op.NOT, itc.next().formula()));
        }

        return result;
    }

    /**
     * Contains.
     * 
     * @param aoe
     *                the aoe
     * @param pv
     *                the pv
     * 
     * @return true, if successful
     */
    private boolean contains(ArrayOfExpression aoe, ProgramVariable pv) {
        for (int i = 0; i < aoe.size(); i++) {
            if (aoe.getExpression(i) == pv) {
                return true;
            }
        }
        return false;

    }

    /**
     * determines and returns the first and active statement if the applied
     * taclet worked on a modality. If the applied taclet performs no symbolic
     * execution <tt>null</tt> is returned
     * 
     * @param node
     *                the node
     * 
     * @return the source element
     */
    public SourceElement determineFirstAndActiveStatement(Node node) {
        final RuleApp ruleApp = node.getAppliedRuleApp();
        SourceElement activeStatement = null;
        if (ruleApp instanceof PosTacletApp) {
            final PosTacletApp pta = (PosTacletApp) ruleApp;
            if (!isSymbolicExecution(pta.taclet())) {
                return null;
            }
            final Term t = pta.posInOccurrence().subTerm();
            final ProgramElement pe = t.executableJavaBlock().program();
            if (pe != null) {
                activeStatement = getActStatement(pe.getFirstElement());
            }
        }
        return activeStatement;
    }

    /**
     * Extract input.
     * 
     * @param n
     *                the n
     * @param pio
     *                the pio
     */
    public void extractInput(Node n, PosInOccurrence pio) {
        JavaBlock jb = this.modalityTopLevel(pio);
        print("Extracting Symbolic Input Values-----------------------");
        ProgramVariable selfPV2 = null;
        MethodBodyStatement mbs = (MethodBodyStatement) this
                .getActStatement(modalityTopLevel(pio).program());
        ReferencePrefix ref = mbs.getMethodReference().getReferencePrefix();

        if (ref instanceof ProgramVariable) {
            setSelfPV((ProgramVariable) ref);
            setStaticMethod(false);
            selfPV2 = (ProgramVariable) ref;

            print("SelfPV " + ref);

        } else {

            final KeYJavaType kjt = ((TypeRef) ref).getKeYJavaType();
            setStaticMethod(true);
            setType((ClassType) kjt.getJavaType());
            print("Static Method of Type " + kjt.getJavaType());

        }

        debuggingMethod = mbs.getProgramMethod(mediator.getServices());
        // debuggingMethod.getVariableSpecification(index)

        ArrayOfExpression args = mbs.getArguments();
        HashMap map = new HashMap();
        HashMap map2 = new HashMap();
        if (jb != null) {
            Term f = pio.constrainedFormula().formula();
            if (f.op() instanceof QuanUpdateOperator) {
                final QuanUpdateOperator op = (QuanUpdateOperator) f.op();
                for (int i = 0; i < op.locationCount(); i++) {
                    if (op.location(f, i).op() instanceof ProgramVariable) {
                        if (contains(args, (ProgramVariable) op.location(f, i)
                                .op())
                                || (selfPV2 != null && selfPV2.equals(op
                                        .location(f, i).op()))) {
                            map.put(op.value(f, i), op.location(f, i));
                            map2.put(op.location(f, i), op.value(f, i));
                        }
                    }
                }

            }

        }

        // set symb input values as list;
        this.symbolicInputValuesAsList = SLListOfTerm.EMPTY_LIST;
        for (int i = 0; i < args.size(); i++) {
            ProgramVariable next = (ProgramVariable) args.getExpression(i);
            Term val = (Term) map2.get(TermFactory.DEFAULT
                    .createVariableTerm(next));// TODO
            this.symbolicInputValuesAsList = this.symbolicInputValuesAsList
                    .append(val);

        }

        setTerm2InputPV(map);
        setInputPV2term(map2);
        print("t2i " + map);
        print("i2t " + map2);
        print("Symbolic Input Values as list " + this.symbolicInputValuesAsList);

    }

    /**
     * Extract precondition.
     * 
     * @param node
     *                the node
     * @param pio
     *                the pio
     */
    public void extractPrecondition(Node node, PosInOccurrence pio) {
        this.precondition = node.sequent().removeFormula(pio).sequent();
    }

    /**
     * Fire debugger event.
     * 
     * @param event
     *                the event
     */
    public void fireDebuggerEvent(DebuggerEvent event) {
        synchronized (listeners) {
            if (event.getType() == DebuggerEvent.TREE_CHANGED) {
                currentTree = (ITNode) event.getSubject();
            } else if (event.getType() == DebuggerEvent.VIS_STATE) {
                currentState = (StateVisualization) event.getSubject();
            }

            Iterator it = listeners.iterator();
            while (it.hasNext()) {
                ((DebuggerListener) it.next()).update(event);
            }
        }
    }

    /**
     * Gets the act statement.
     * 
     * @param statement
     *                the statement
     * 
     * @return the act statement
     */
    private SourceElement getActStatement(SourceElement statement) {
        while ((statement instanceof ProgramPrefix)
                || statement instanceof ProgramElementName) {
            if (statement instanceof LabeledStatement) {
                statement = ((LabeledStatement) statement).getBody();
            } else if (statement == statement.getFirstElement()) {
                break;
            } else {
                statement = statement.getFirstElement();
            }
        }
        return statement;
    }

    /**
     * Gets the array index.
     * 
     * @param pio2
     *                the pio2
     * 
     * @return the array index
     */
    public SetOfTerm getArrayIndex(PosInOccurrence pio2) {
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        PosInOccurrence pio = pio2;
        if (pio.constrainedFormula().formula().op() instanceof QuanUpdateOperator) {
            QuanUpdateOperator op = (QuanUpdateOperator) pio
                    .constrainedFormula().formula().op();
            Term f = pio.constrainedFormula().formula();
            for (int i = 0; i < op.locationCount(); i++) {
                Term t = (op.location(f, i));

                if (t.op() instanceof ArrayOp) {
                    result = result.add(t.sub(1));
                }
            }

        } else
            throw new RuntimeException("Expected QuanUpd as top op");
        return result;
    }

    /**
     * Gets the array locations.
     * 
     * @param pio2
     *                the pio2
     * 
     * @return the array locations
     */
    public SetOfTerm getArrayLocations(PosInOccurrence pio2) {
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        PosInOccurrence pio = pio2;
        if (pio.constrainedFormula().formula().op() instanceof QuanUpdateOperator) {
            QuanUpdateOperator op = (QuanUpdateOperator) pio
                    .constrainedFormula().formula().op();
            Term f = pio.constrainedFormula().formula();
            for (int i = 0; i < op.locationCount(); i++) {
                Term t = (op.location(f, i));

                if (t.op() instanceof ArrayOp) {
                    result = result.add(t);
                }
            }

        } else
            throw new RuntimeException("Expected QuanUpd as top op");
        return result;
    }

    /**
     * Gets the bp manager.
     * 
     * @return the bp manager
     */
    public BreakpointManager getBpManager() {
        return bpManager;
    }

    /**
     * Gets the current state.
     * 
     * @return the current state
     */
    public StateVisualization getCurrentState() {
        return currentState;
    }

    /**
     * Gets the current tree.
     * 
     * @return the current tree
     */
    public ITNode getCurrentTree() {
        return ExecutionTree.getITNode();
    }

    /**
     * Gets the debugging method.
     * 
     * @return the debugging method
     */
    public ProgramMethod getDebuggingMethod() {
        return debuggingMethod;
    }

    /**
     * Gets the execution terminated normal.
     * 
     * @param n
     *                the n
     * 
     * @return the execution terminated normal
     */
    public PosInOccurrence getExecutionTerminatedNormal(Node n) {
        final Sequent s = n.sequent();
        for (IteratorOfConstrainedFormula it = s.succedent().iterator(); it
                .hasNext();) {
            ConstrainedFormula cfm = it.next();
            final Term f = cfm.formula();
            if (f.op() instanceof QuanUpdateOperator) {
                final Term subOp = f.sub(f.arity() - 1);
                if (subOp.op() == postPredicate) {
                    return new PosInOccurrence(cfm, PosInTerm.TOP_LEVEL, false);
                }
            }
        }
        return null;
    }

    /**
     * term 2 term.
     * 
     * @return the input p v2term
     */
    public HashMap getInputPV2term() {
        return inputPV2term;
    }

    /**
     * Gets the locations.
     * 
     * @param pio2
     *                the pio2
     * 
     * @return the locations
     */
    public ListOfTerm getLocations(PosInOccurrence pio2) {
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;
        PosInOccurrence pio = pio2;

        if (pio.constrainedFormula().formula().op() instanceof QuanUpdateOperator) {
            QuanUpdateOperator op = (QuanUpdateOperator) pio
                    .constrainedFormula().formula().op();
            Term f = pio.constrainedFormula().formula();
            for (int i = 0; i < op.locationCount(); i++) {
                Term t = (op.location(f, i));
                if (t.op() instanceof AttributeOp /*
                                                     * && !((ProgramVariable)
                                                     * ((AttributeOp)
                                                     * t.op()).attribute()).isImplicit()
                                                     */) {
                    result = result.append(t);
                } else if (t.op() instanceof ProgramVariable) {
                    final ProgramVariable pv = (ProgramVariable) t.op();
                    KeYJavaType kjt = pv.getContainerType();
                    if (kjt != null) {
                        result = result.append(t);
                    }
                } else if (t.op() instanceof ArrayOp) {
                    result = result.append(t);
                }
            }

        } else {
            throw new RuntimeException("Expected QuanUpd as top op");
        }
        return result;
    }

    /**
     * Gets the mediator.
     * 
     * @return the mediator
     */
    public KeYMediator getMediator() {
        return mediator;
    }

    /**
     * Gets the method frame.
     * 
     * @param context
     *                the context
     * 
     * @return the method frame
     */
    public MethodFrame getMethodFrame(SourceElement context) {
        MethodFrame frame = null;
        if (context instanceof ProgramPrefix) {
            final ArrayOfProgramPrefix prefixElements = ((ProgramPrefix) context)
                    .getPrefixElements();
            for (int i = 0, len = prefixElements.size(); i < len; i++) {
                if (prefixElements.getProgramPrefix(i) instanceof MethodFrame) {
                    frame = (MethodFrame) prefixElements.getProgramPrefix(i);
                }
            }
        }
        return frame;
    }

    /**
     * Gets the method stack size.
     * 
     * @param n
     *                the n
     * 
     * @return the method stack size
     */
    public int getMethodStackSize(Node n) {
        final PosInOccurrence pio = this.getProgramPIO(n.sequent());
        if (pio == null) {
            return -1;
        }
        return this.getMethodStackSize(modalityTopLevel(pio).program());
    }

    /**
     * computes the depth of the method frame stack up to the first active
     * statement.
     * 
     * @param context
     *                the context
     * 
     * @return the method stack size
     */
    private int getMethodStackSize(SourceElement context) {
        int size = 0;
        if (context instanceof ProgramPrefix) {
            final ArrayOfProgramPrefix prefixElements = ((ProgramPrefix) context)
                    .getPrefixElements();
            for (int i = 0, len = prefixElements.size(); i < len; i++)
                if (prefixElements.getProgramPrefix(i) instanceof MethodFrame) {
                    size++;
                }
        }
        return size;
    }

    /**
     * Gets the node for tc.
     * 
     * @param file
     *                the file
     * @param method
     *                the method
     * 
     * @return the node for tc
     */
    public Node getNodeForTC(String file, String method) {
        Object result = tc2node.get(new TestCaseIdentifier(file, method));
        if (result instanceof Node) {
            return (Node) result;
        }
        return null;
    }

    /**
     * Gets the param.
     * 
     * @param mbs
     *                the mbs
     * 
     * @return the param
     */
    public HashSet getParam(MethodBodyStatement mbs) {
        HashSet result = new HashSet();
        for (int i = 0; i < mbs.getArguments().size(); i++) {
            result.add(mbs.getArguments().getExpression(i));
        }
        return result;
    }

    /**
     * Gets the post predicate.
     * 
     * @return the post predicate
     */
    public Function getPostPredicate() {
        return postPredicate;
    }

    /**
     * Gets the precondition.
     * 
     * @return the precondition
     */
    public Sequent getPrecondition() {
        return precondition;
    }

    /**
     * Gets the program counter.
     * 
     * @param jb
     *                the jb
     * 
     * @return the program counter
     */
    public SourceElementId getProgramCounter(JavaBlock jb) {
        SourceElement se = getActStatement(jb.program());
        if (se != null && se instanceof MethodReference) {
            MethodReference mr = (MethodReference) se;
            // mr.getT
            if (mr.getMethodName().toString().equals(sepName)
                    && mr.getArgumentAt(0) instanceof IntLiteral) {
                MethodFrame mf = getMethodFrame(jb.program());
                if (mf == null)
                    return null;
                ExecutionContext ec = (ExecutionContext) mf
                        .getExecutionContext();
                return new SourceElementId(ec.getTypeReference().toString(),
                        ((IntLiteral) (mr.getArgumentAt(0))).getValue());
            }

        }
        return null;

    }

    /**
     * Gets the program counter.
     * 
     * @param n
     *                the n
     * 
     * @return the program counter
     */
    public SourceElementId getProgramCounter(Node n) {
        IteratorOfPosInOccurrence it = n.getNodeInfo().getVisualDebuggerState()
                .getLabels().keyIterator();
        JavaBlock jb = null;
        SourceElement se = null;
        while (it.hasNext()) {
            PosInOccurrence pio = it.next();
            jb = modalityTopLevel(pio); // TODO !!!!!!!!!!!!!!!!!!!!!!
            if (jb != null) {
                se = getActStatement(jb.program());
                break;
            }
        }

        if (jb != null && se != null && se instanceof MethodReference) {
            MethodReference mr = (MethodReference) se;
            if (mr.getMethodName().toString().equals(sepName)
                    && mr.getArgumentAt(0) instanceof IntLiteral) {
                MethodFrame mf = getMethodFrame(jb.program());
                if (mf == null)
                    return null;
                ExecutionContext ec = (ExecutionContext) mf
                        .getExecutionContext();
                return new SourceElementId(ec.getTypeReference().toString(),
                        ((IntLiteral) (mr.getArgumentAt(0))).getValue());
            }

        }
        return null;
    }

    /**
     * Gets the program counter.
     * 
     * @param pio
     *                the pio
     * 
     * @return the program counter
     */
    public SourceElementId getProgramCounter(PosInOccurrence pio) {
        final JavaBlock jb = modalityTopLevel(pio);
        if (jb != null) {
            return this.getProgramCounter(jb);
        }
        return null;

    }

    /**
     * Gets the program pio.
     * 
     * @param s
     *                the s
     * 
     * @return the program pio
     */
    public PosInOccurrence getProgramPIO(Sequent s) {
        IteratorOfConstrainedFormula it = s.succedent().iterator();
        while (it.hasNext()) {
            PosInOccurrence pio = new PosInOccurrence(it.next(),
                    PosInTerm.TOP_LEVEL, false);

            if (modalityTopLevel(pio) != null) {
                return pio;
            }
        }
        return null;

    }

    /**
     * Gets the run limit.
     * 
     * @return the run limit
     */
    public int getRunLimit() {
        return runLimit;
    }

    /**
     * Gets the self pv.
     * 
     * @return the self pv
     */
    public ProgramVariable getSelfPV() {
        return selfPV;
    }

    /**
     * Gets the self term.
     * 
     * @return the self term
     */
    public Term getSelfTerm() {
        return TermFactory.DEFAULT.createVariableTerm(selfPV);
    }

    /**
     * Gets the symbolic input values.
     * 
     * @return the symbolic input values
     */
    public SetOfTerm getSymbolicInputValues() {
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        for (Iterator it = this.term2InputPV.keySet().iterator(); it.hasNext();) {
            result = result.add((Term) it.next());
        }
        return result;

    }

    /**
     * Gets the symbolic input values as list.
     * 
     * @return the symbolic input values as list
     */
    public ListOfTerm getSymbolicInputValuesAsList() {
        return this.symbolicInputValuesAsList;
    }

    /**
     * Gets the term2 input pv.
     * 
     * @return the term2 input pv
     */
    public HashMap getTerm2InputPV() {
        return term2InputPV;
    }

    /**
     * Gets the type.
     * 
     * @return the type
     */
    public ClassType getType() {
        return type;
    }

    /**
     * Gets the values for location.
     * 
     * @param locs
     *                set of Terms (ops)
     * @param pio
     *                the pio
     * 
     * @return term2term
     */
    public HashMap getValuesForLocation(HashSet locs, PosInOccurrence pio) {
        HashMap result = new HashMap();

        Term f = pio.constrainedFormula().formula();
        if (f.op() instanceof QuanUpdateOperator) {
            final QuanUpdateOperator op = (QuanUpdateOperator) f.op();
            for (int i = 0; i < op.locationCount(); i++) {
                if (op.location(f, i).op() instanceof ProgramVariable) {
                    if (locs.contains(op.location(f, i).op())
                            || (selfPV != null && selfPV.equals(op.location(f,
                                    i).op()))) {

                        result.put(op.location(f, i), op.value(f, i));

                    }

                }
            }

        }

        return result;
    }

    /**
     * Initialize.
     */
    public void initialize() {

        UpdateLabelListener lListener = new UpdateLabelListener();
        // lListener.setListeners(listeners);
        Goal.addRuleAppListener(lListener);
        mediator.setMaxAutomaticSteps(20000);

        // Extract ProgramVariables of the context program
        JavaInfo info = mediator.getServices().getJavaInfo();
        Set kjts = info.getAllKeYJavaTypes();
        // info.getKeYProgModelInfo().getMethods(ct)
        HashSet pvs = new HashSet();
        for (Iterator it = kjts.iterator(); it.hasNext();) {
            KeYJavaType kjt = (KeYJavaType) it.next();
            if (kjt.getJavaType() instanceof ClassDeclaration) {
                final ListOfProgramMethod methods = info
                        .getAllProgramMethods(kjt);
                for (IteratorOfProgramMethod mit = methods.iterator(); mit
                        .hasNext();) {
                    ProgramMethod m = mit.next();

                    if (m != null) {
                        ProgramVariableCollector pvc = new ProgramVariableCollector(
                                m);
                        pvc.start();
                        pvs.addAll(pvc.result());
                    }

                }
            }
        }

        final Proof proof = mediator.getProof();
        ExecutionTree pl = new ExecutionTree(proof, mediator, true);
        pl.setListeners(listeners);
        mediator.addAutoModeListener(pl);

        this.initPhase = true;
        bpManager.setNoEx(true);

        postPredicate = (Function) proof.getNamespaces().functions().lookup(
                POST_PREDICATE_NAME);
        setProofStrategy(proof, true, false, SLListOfTerm.EMPTY_LIST);
        run();
    }

    /**
     * Checks if is inits the phase.
     * 
     * @return true, if is inits the phase
     */
    public boolean isInitPhase() {
        return initPhase;
    }

    /**
     * Checks if is sep statement.
     * 
     * @param pe
     *                the pe
     * 
     * @return true, if is sep statement
     */
    public boolean isSepStatement(ProgramElement pe) {
        if (pe instanceof MethodReference) {
            MethodReference mr = (MethodReference) pe;
            if (mr.getMethodName().toString().equals(sepName))
                return true;

        }
        return false;

    }

    /**
     * Checks if is static method.
     * 
     * @return true, if is static method
     */
    public boolean isStaticMethod() {
        return staticMethod;
    }

    /**
     * Checks if is symbolic execution.
     * 
     * @param t
     *                the t
     * 
     * @return true, if is symbolic execution
     */
    private boolean isSymbolicExecution(Taclet t) {
        ListOfRuleSet list = t.getRuleSets();
        RuleSet rs;
        while (!list.isEmpty()) {
            rs = list.head();
            Name name = rs.name();
            if (symbolicExecNames.contains(name))
                return true;
            list = list.tail();
        }
        return false;
    }

    /**
     * Modality top level.
     * 
     * @param pio
     *                the pio
     * 
     * @return the java block
     */
    public JavaBlock modalityTopLevel(PosInOccurrence pio) {
        Term cf = pio.constrainedFormula().formula();
        if (cf.arity() > 0) {
            // CHECK: if --> while ?
            if (cf.op() instanceof QuanUpdateOperator) {
                cf = ((QuanUpdateOperator) cf.op()).target(cf);
            }
            if (cf.op() instanceof Modality) {
                return cf.javaBlock();
            }
        }
        return null;
    }

    /**
     * Pretty print.
     * 
     * @param l
     *                the l
     * 
     * @return the string
     */
    public String prettyPrint(ListOfTerm l) {
        // KeYMediator mediator=
        // VisualDebugger.getVisualDebugger().getMediator();
        final LogicPrinter lp = new DebuggerLP(new ProgramPrinter(null),
                mediator.getNotationInfo(), mediator.getServices(),
                term2InputPV);

        String result = "";
        IteratorOfTerm it = l.iterator();
        while (it.hasNext()) {
            try {
                lp.printTerm(it.next());
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
            result = result + lp.toString();
            lp.reset();
            if (it.hasNext())
                result = result + " AND ";

        }
        mediator.getNotationInfo().setAbbrevMap(new AbbrevMap());
        return removeLineBreaks(result);
    }

    /**
     * Pretty print.
     * 
     * @param l
     *                the l
     * @param objects
     *                the objects
     * @param thisObject
     *                the this object
     * 
     * @return the string
     */
    public String prettyPrint(ListOfTerm l, LinkedList objects,
            SymbolicObject thisObject) {
        // KeYMediator mediator=
        // VisualDebugger.getVisualDebugger().getMediator();
        final LogicPrinter lp = new DebuggerLP(new ProgramPrinter(null),
                mediator.getNotationInfo(), mediator.getServices(),
                term2InputPV, objects, thisObject);

        String result = "";
        IteratorOfTerm it = l.iterator();
        while (it.hasNext()) {
            try {
                lp.printTerm(it.next());
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
            result = result + lp.toString();
            lp.reset();
            if (it.hasNext())
                result = result + " AND ";

        }
        mediator.getNotationInfo().setAbbrevMap(new AbbrevMap());
        return removeLineBreaks(result);
    }

    /**
     * Pretty print.
     * 
     * @param l
     *                the l
     * @param objects
     *                the objects
     * @param thisObject
     *                the this object
     * 
     * @return the string
     */
    public String prettyPrint(SetOfTerm l, LinkedList objects,
            SymbolicObject thisObject) {
        return prettyPrint(SLListOfTerm.EMPTY_LIST.append(l.toArray()),
                objects, thisObject);
    }

    /**
     * Pretty print.
     * 
     * @param l
     *                the l
     * 
     * @return the string
     */
    public String prettyPrint(Term l) {
        // KeYMediator mediator=
        // VisualDebugger.getVisualDebugger().getMediator();
        final LogicPrinter lp = new DebuggerLP(new ProgramPrinter(null),
                mediator.getNotationInfo(), mediator.getServices(),
                term2InputPV);

        String result = "";

        try {
            lp.printTerm(l);
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        result = result + lp.toString();

        mediator.getNotationInfo().setAbbrevMap(new AbbrevMap());
        return removeLineBreaks(result);
    }

    // TODO {u}POST, execution is finished...
    // alternative: { } <sep(-1);>\phi

    /**
     * Pretty print.
     * 
     * @param l
     *                the l
     * @param sos
     *                the sos
     * @param so
     *                the so
     * 
     * @return the string
     */
    public String prettyPrint(Term l, LinkedList sos, SymbolicObject so) {
        final LogicPrinter lp = new DebuggerLP(new ProgramPrinter(null),
                mediator.getNotationInfo(), mediator.getServices(),
                term2InputPV, sos, so);

        String result = "";

        try {
            lp.printTerm(l);
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        result = result + lp.toString();

        mediator.getNotationInfo().setAbbrevMap(new AbbrevMap());
        return removeLineBreaks(result);
    }

    /**
     * Prints the test cases.
     */
    public void printTestCases() {
        print(this.tc2node.toString());
    }

    /**
     * Refresh rule apps.
     */
    private void refreshRuleApps() {
        ListOfGoal goals = mediator.getProof().openGoals();
        // g.getRuleAppManager().clearCache();
        IteratorOfGoal it = goals.iterator();
        while (it.hasNext()) {
            Goal g = it.next();
            g.ruleAppIndex().clearIndexes();
            g.ruleAppIndex().fillCache();
        }

    }

    /**
     * Removes the implicite.
     * 
     * @param list
     *                the list
     * 
     * @return the list of term
     */
    public ListOfTerm removeImplicite(ListOfTerm list) {
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;

        for (IteratorOfTerm it = list.iterator(); it.hasNext();) {
            final Term n = it.next();
            if (!VisualDebugger.containsImplicitAttr(n))
                result = result.append(n);

        }
        return result;
    }

    /**
     * Removes the line breaks.
     * 
     * @param s
     *                the s
     * 
     * @return the string
     */
    private String removeLineBreaks(String s) {
        return s.replace('\n', ' ');
    }

    /**
     * Removes the step over.
     * 
     * @param goals
     *                the goals
     */
    private void removeStepOver(ListOfGoal goals) {
        IteratorOfGoal it = goals.iterator();
        while (it.hasNext()) {
            Node next = it.next().node();
            next.getNodeInfo().getVisualDebuggerState().setStepOver(-1);
            next.getNodeInfo().getVisualDebuggerState().setStepOverFrom(-1);
            print("StepOver of " + next.serialNr() + " set to -1");
        }

    }

    /**
     * Run.
     * 
     * @return true, if successful
     */
    public boolean run() {
        // this.refreshRuleApps();
        if (!mediator.autoMode()) {
            run(mediator.getProof().openGoals());
            return true;
        } else {
            return false;
        }
    }

    /**
     * Run.
     * 
     * @param goals
     *                the goals
     * 
     * @return true, if successful
     */
    public boolean run(ListOfGoal goals) {
        if (!mediator.autoMode()) {
            this.removeStepOver(goals);
            this.setSteps(goals, this.runLimit);
            
            setProofStrategy(mediator.getProof(), true, false,
                   watchPointManager.getListOfWatchpoints());
            runProver(goals);

            return true;
        }
        return false;
    }

    /**
     * Run prover.
     * 
     * @param goals
     *                the goals
     */
    private void runProver(final ListOfGoal goals) {
        this.refreshRuleApps();
        mediator.startAutoMode(goals);
        // mediator.getInteractiveProver().removeProverTaskListener(proverTaskListener);

    }

    /**
     * Sets the inits the phase.
     * 
     * @param initPhase
     *                the new inits the phase
     */
    public void setInitPhase(boolean initPhase) {
        this.initPhase = initPhase;
    }

    /**
     * Sets the input p v2term.
     * 
     * @param inputPV2term
     *                the new input p v2term
     */
    public void setInputPV2term(HashMap inputPV2term) {
        this.inputPV2term = inputPV2term;
    }

    /**
     * Sets the proof strategy.
     * 
     * @param proof
     *                the proof
     * @param splittingAllowed
     *                the splitting allowed
     * @param inUpdateAndAssumes
     *                the in update and assumes
     */
    public void setProofStrategy(final Proof proof, boolean splittingAllowed,
            boolean inUpdateAndAssumes, ListOfTerm watchpoints) {

        StrategyProperties strategyProperties = DebuggerStrategy
                .getDebuggerStrategyProperties(splittingAllowed,
                        inUpdateAndAssumes, isInitPhase(), watchpoints);

        final StrategyFactory factory = new DebuggerStrategy.Factory();
        proof.setActiveStrategy((factory.create(proof, strategyProperties)));
    }

    /**
     * Sets the self pv.
     * 
     * @param selfPV
     *                the new self pv
     */
    public void setSelfPV(ProgramVariable selfPV) {
        this.selfPV = selfPV;
    }

    /**
     * Sets the static method.
     * 
     * @param staticMethod
     *                the new static method
     */
    public void setStaticMethod(boolean staticMethod) {
        this.staticMethod = staticMethod;
    }

    /**
     * Sets the step over.
     * 
     * @param goals
     *                the new step over
     */
    private void setStepOver(ListOfGoal goals) {
        IteratorOfGoal it = goals.iterator();
        while (it.hasNext()) {
            Node next = it.next().node();
            final int size = this.getMethodStackSize(next);
            next.getNodeInfo().getVisualDebuggerState().setStepOver(size);
            next.getNodeInfo().getVisualDebuggerState().setStepOverFrom(
                    next.serialNr());
            print("StepOver of " + next.serialNr() + " set to " + size);
            // nodes = nodes.prepend();
        }

    }

    /**
     * Sets the steps.
     * 
     * @param goals
     *                the goals
     * @param steps
     *                the steps
     */
    private void setSteps(ListOfGoal goals, int steps) {
        IteratorOfGoal it = goals.iterator();
        while (it.hasNext()) {
            Node next = it.next().node();
            if (!next.root())
                next.parent().getNodeInfo().getVisualDebuggerState()
                        .setStatementIdcount(steps);
            next.getNodeInfo().getVisualDebuggerState().setStatementIdcount(
                    steps);
            print("Steps of " + next.serialNr() + " set to " + steps);
            // nodes = nodes.prepend();
        }

    }

    /**
     * Sets the term2 input pv.
     * 
     * @param inputValues
     *                the new term2 input pv
     */
    public void setTerm2InputPV(HashMap inputValues) {
        this.term2InputPV = inputValues;
    }

    /**
     * Sets the type.
     * 
     * @param type
     *                the new type
     */
    public void setType(ClassType type) {
        this.type = type;
    }

    /**
     * Simplify.
     * 
     * @param terms
     *                the terms
     * 
     * @return the list of term
     */
    public ListOfTerm simplify(ListOfTerm terms) {
        if (terms.size() == 0)
            return terms;
        final DebuggerPO po = new DebuggerPO("DebuggerPo");
        final ProofStarter ps = new ProofStarter();
        if (etProgressMonitor != null) {
            ps.addProgressMonitor(etProgressMonitor);
        }
        po.setTerms(terms);

        final ProofEnvironment proofEnvironment = mediator.getProof().env();
        final InitConfig initConfig = proofEnvironment.getInitConfig();

        po.setIndices(initConfig.createTacletIndex(), initConfig
                .createBuiltInRuleIndex());
        po.setProofSettings(mediator.getProof().getSettings());
        po.setConfig(initConfig);
        po.setTerms(terms);
        ps.init(po);

        final Proof proof = ps.getProof();

        setProofStrategy(proof, false, false, SLListOfTerm.EMPTY_LIST);
        ps.setUseDecisionProcedure(useDecisionProcedures);
        ps.run(proofEnvironment);

        setProofStrategy(proof, true, false, SLListOfTerm.EMPTY_LIST);
        if (etProgressMonitor != null) {
            ps.removeProgressMonitor(etProgressMonitor);
        }
        return collectResult(proof.openGoals().iterator().next().node()
                .sequent());
    }

    /**
     * Start thread.
     * 
     * @param r
     *                the r
     */
    private void startThread(final Runnable r) {
        mediator.stopInterface(false);
        Thread appThread = new Thread() {
            public void run() {
                try {
                    SwingUtilities.invokeAndWait(r);
                    // worker.start();
                } catch (Exception e) {
                    e.printStackTrace();
                }
                mediator.startInterface(false);
                mediator.setInteractive(true);
                print("Finished on " + Thread.currentThread());
            }
        };
        appThread.start();
    }

    /**
     * Step into.
     * 
     * @return true, if successful
     */
    public boolean stepInto() {
        return stepInto(mediator.getProof().openGoals());
    }

    /**
     * Step into.
     * 
     * @param goals
     *                the goals
     * 
     * @return true, if successful
     */
    public boolean stepInto(ListOfGoal goals) {
        return this.stepInto(goals, 1);
    }

    /**
     * Step into.
     * 
     * @param goals
     *                the goals
     * @param steps
     *                the steps
     * 
     * @return true, if successful
     */
    public boolean stepInto(ListOfGoal goals, int steps) {
        if (!mediator.autoMode()) {
            final Proof proof = mediator.getProof();
            removeStepOver(proof.openGoals());
            this.setSteps(goals, steps);
            setProofStrategy(proof, true, false, watchPointManager.getListOfWatchpoints());
            runProver(goals);
            return true;
        }
        return false;
    }

    /**
     * Step over.
     */
    public void stepOver() {
        this.stepOver(mediator.getProof().openGoals());
    }

    /**
     * Step over.
     * 
     * @param goals
     *                the goals
     */
    public void stepOver(ListOfGoal goals) {
        setStepOver(goals);
        this.setSteps(goals, runLimit);
        setProofStrategy(mediator.getProof(), true, false,
                watchPointManager.getListOfWatchpoints());
        runProver(goals);
    }

    /**
     * Step to first sep.
     * 
     * @return true, if successful
     */
    public boolean stepToFirstSep() {
        if (!mediator.autoMode()) {

            final Proof proof = mediator.getProof();
            removeStepOver(proof.openGoals());
            setSteps(proof.openGoals(), 0);
            setProofStrategy(proof, true, false, watchPointManager.getListOfWatchpoints());
            runProver(proof.openGoals());
            return true;
        }
        return false;
    }

    /**
     * Visualize.
     * 
     * @param n
     *                the n
     */
    public synchronized void visualize(ITNode n) {
        mediator = main.mediator();
        final ITNode node = n;

        final Runnable interfaceSignaller = new Runnable() {
            public void run() {
                new StateVisualization(node, mediator,
                        maxProofStepsForStateVisComputation,
                        useDecisionProcedures);
            }
        };
        startThread(interfaceSignaller);
    }

    /**
     * The Class TestCaseIdentifier.
     */
    public class TestCaseIdentifier {

        /** The file. */
        private final String file;

        /** The method. */
        private final String method;

        /**
         * Instantiates a new test case identifier.
         * 
         * @param file
         *                the file
         * @param method
         *                the method
         */
        public TestCaseIdentifier(String file, String method) {
            this.file = file;
            this.method = method;
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.lang.Object#equals(java.lang.Object)
         */
        public boolean equals(Object o) {
            if (o instanceof TestCaseIdentifier) {
                TestCaseIdentifier tci = (TestCaseIdentifier) o;
                return file.equals(tci.getFile())
                        && method.equals(tci.getMethod());
            }

            return false;
        }

        /**
         * Gets the file.
         * 
         * @return the file
         */
        public String getFile() {
            return file;
        }

        /**
         * Gets the method.
         * 
         * @return the method
         */
        public String getMethod() {
            return method;
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.lang.Object#hashCode()
         */
        public int hashCode() {
            return (method.concat(file)).hashCode();
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.lang.Object#toString()
         */
        public String toString() {
            return "File: " + file + " Method: " + method;
        }
    }

    /**
     * Adds the pm to proof starter.
     * 
     * @param pm
     *                the pm
     */
    public void addPMtoProofStarter(ProgressMonitor pm) {
        this.etProgressMonitor = pm;
        ETProverTaskListener proverTaskListener = new ETProverTaskListener(
                etProgressMonitor);
        mediator.getInteractiveProver().addProverTaskListener(
                proverTaskListener);

    }

    /**
     * The Nested Class ETProverTaskListener.
     * 
     * Implements the ProverTaskListener Interface. Serves as wrapper for the
     * ExcecutionTreeView's progressmonitor. The Instance of
     * ETProverTaskListener is registered to the KeYMediator.
     */
    static class ETProverTaskListener implements ProverTaskListener {

        /** The pm. */
        private ProgressMonitor pm = null;

        /**
         * Instantiates a new PM.
         * 
         * @param pm
         *                the ProgressMonitor
         */
        public ETProverTaskListener(ProgressMonitor pm) {
            this.pm = pm;
        }

        // reset progressbar when task is finished
        /*
         * (non-Javadoc)
         * 
         * @see de.uka.ilkd.key.gui.ProverTaskListener#taskFinished()
         */
        public void taskFinished() {
            pm.setProgress(300);
        }

        /*
         * (non-Javadoc)
         * 
         * @see de.uka.ilkd.key.gui.ProverTaskListener#taskProgress(int)
         */
        public void taskProgress(int position) {

            pm.setProgress(position);
        }

        /*
         * (non-Javadoc)
         * 
         * @see de.uka.ilkd.key.gui.ProverTaskListener#taskStarted(java.lang.String,
         *      int)
         */
        public void taskStarted(String message, int size) {
            // System.out.println("taskStarted -size:" + size);
            pm.setMaximum(300);

        }
    }

    public WatchPointManager getWatchPointManager() {
        return watchPointManager;
    }

    public void setWatchPointManager(WatchPointManager watchPointManager) {
        this.watchPointManager = watchPointManager;
    }


}
