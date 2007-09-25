package de.uka.ilkd.key.visualdebugger;

import java.io.File;
import java.io.IOException;
import java.util.*;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.ArrayOfExpression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
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
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IteratorOfGoal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.strategy.DebuggerStrategy;
import de.uka.ilkd.key.strategy.feature.InUpdateFeature;

public class VisualDebugger {
    public static final String debugClass = "Debug";

    private static boolean debuggingMode = false;

    public static final String debugPackage = "visualdebugger";

    static boolean keyBuggerMode;

    public static boolean quan_splitting = false;

    public static final String sepName = "sep";

    public static boolean showImpliciteAttr = false;

    public static boolean showMainWindow = false;

    private static VisualDebugger singleton;

    private static List symbolicExecNames = new ArrayList(5);

    public static final String tempDir = System.getProperty("user.home")
            + File.separator + "tmp" + File.separator + "visualdebugger"
            + File.separator;

    public static final boolean vdInDebugMode = false;

    static {
        symbolicExecNames.add(new Name("simplify_prog"));
        symbolicExecNames.add(new Name("simplify_autoname"));
        symbolicExecNames.add(new Name("simplify_int"));
        symbolicExecNames.add(new Name("simplify_object_creation"));
        symbolicExecNames.add(new Name("method_expand"));
    }

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

    public static VisualDebugger getVisualDebugger() {
        if (singleton == null) {
            singleton = new VisualDebugger();
            String[] args = new String[2];

            args[0] = "DEBUGGER";
            args[1] = "LOOP";
            // args[1]= "DEBUsG";
            // Main.main(args);
            Main.evaluateOptions(args);
            Main key = Main.getInstance(false);
            key.loadCommandLineFile();

            singleton.main = Main.getInstance(false);
            singleton.mediator = singleton.main.mediator();
            // singleton.ip = singleton.mediator.getInteractiveProver();

        }
        return singleton;
    }

    public static boolean isDebuggingMode() {
        return debuggingMode;
    }

    public static void print(Object o) {
        if (vdInDebugMode)
            System.out.println(o.toString());
    }

    public static void print(String s) {
        if (vdInDebugMode)
            System.out.println(s);
    }

    public static void setDebuggingMode(boolean mode) {
        debuggingMode = mode;
    }

    private BreakpointManager bpManager;

    private StateVisualization currentState;

    private ITNode currentTree;

    private ProgramMethod debuggingMethod;

    private boolean determinePostValue = false;

    private boolean initPhase = false;

    private HashMap inputPV2term = new HashMap();

    private LinkedList listeners = new LinkedList();

    private Main main;

    // InteractiveProver ip;
    private KeYMediator mediator;

    private Sequent precondition;

    private int runLimit = 5;

    private ProgramVariable selfPV;

    private boolean staticMethod;

    private ListOfTerm symbolicInputValuesAsList = SLListOfTerm.EMPTY_LIST;

    private HashMap tc2node = new HashMap();

    private HashMap term2InputPV = new HashMap();

    private ClassType type;

    protected VisualDebugger() {
        bpManager = new BreakpointManager(this);

        // main = Main.getInstance();
    }

    public void addListener(DebuggerListener listener) {
        listeners.add(listener);
    }

    public void addTestCase(String file, String method, Node n) {
        tc2node.put(new TestCaseIdentifier(file, method), n);

    }

    public ListOfProgramVariable arrayOfExpression2ListOfProgVar(
            ArrayOfExpression aoe, int start) {
        ListOfProgramVariable lopv = SLListOfProgramVariable.EMPTY_LIST;
        for (int i = start; i < aoe.size(); i++) {
            lopv = lopv.append((ProgramVariable) aoe.getExpression(i));
        }
        return lopv;
    }

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

    private boolean contains(ArrayOfExpression aoe, ProgramVariable pv) {
        for (int i = 0; i < aoe.size(); i++) {
            if (aoe.getExpression(i) == pv) {
                return true;
            }
        }
        return false;

    }

    /**
     * determines the first and active statement if the applied taclet worked on
     * a modality
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

    public void extractPrecondition(Node node, PosInOccurrence pio) {
        this.precondition = node.sequent().removeFormula(pio).sequent();
    }

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

    private SourceElement getActStatement(SourceElement statement) {
        while ((statement instanceof ProgramPrefix)
                || statement instanceof ProgramElementName) {
            if (statement instanceof LabeledStatement)
                statement = ((LabeledStatement) statement).getBody();
            else if (statement == statement.getFirstElement()) {
                return statement;
            } else {
                statement = statement.getFirstElement();
            }
        }
        return statement;
    }

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

    public BreakpointManager getBpManager() {
        return bpManager;
    }

    public StateVisualization getCurrentState() {
        return currentState;
    }

    public ITNode getCurrentTree() {
        return ExecutionTree.getITNode();
    }

    public ProgramMethod getDebuggingMethod() {
        return debuggingMethod;
    }

    public PosInOccurrence getExecutionTerminatedNormal(Node n) {
        final Sequent s = n.sequent();
        for (IteratorOfConstrainedFormula it = s.succedent().iterator(); it
                .hasNext();) {
            ConstrainedFormula cfm = it.next();
            final Term f = cfm.formula();
            if (f.op() instanceof QuanUpdateOperator) {
                final Term subOp = f.sub(f.arity() - 1);
                if (subOp.op().name().toString().equals("POST")
                        && subOp.javaBlock() == JavaBlock.EMPTY_JAVABLOCK) {
                    return new PosInOccurrence(cfm, PosInTerm.TOP_LEVEL, false);
                }

            }

        }
        return null;
    }

    /**
     * term 2 term
     * 
     * @return
     */
    public HashMap getInputPV2term() {
        return inputPV2term;
    }

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

    public KeYMediator getMediator() {
        return mediator;
    }

    public MethodFrame getMethodFrame(SourceElement context) {
        MethodFrame frame = null;
        if (context instanceof ProgramPrefix) {            
            final ArrayOfProgramPrefix prefixElements = 
                ((ProgramPrefix)context).getPrefixElements();
            for (int i = 0, len = prefixElements.size(); i<len; i++) {
              if (prefixElements.getProgramPrefix(i) instanceof MethodFrame) {
                  frame = (MethodFrame) prefixElements.getProgramPrefix(i);
              }
            }
        }
        return frame;
    }

    public int getMethodStackSize(Node n) {
        final PosInOccurrence pio = this.getProgramPIO(n.sequent());
        if (pio == null) {
            return -1;
        }
        return this.getMethodStackSize(modalityTopLevel(pio).program());
    }

    /**
     * computes the depth of the method frame stack up to the first active
     * statement
     */
    private int getMethodStackSize(SourceElement context) {
        int size = 0;       
        if (context instanceof ProgramPrefix) {            
          final ArrayOfProgramPrefix prefixElements = 
              ((ProgramPrefix)context).getPrefixElements();
          for (int i = 0, len = prefixElements.size(); i<len; i++)
            if (prefixElements.getProgramPrefix(i) instanceof MethodFrame) {
                size++;
            }
        }
        return size;
    }

    public Node getNodeForTC(String file, String method) {
        Object result = tc2node.get(new TestCaseIdentifier(file, method));
        if (result instanceof Node) {
            return (Node) result;
        }
        return null;        
    }

    public HashSet getParam(MethodBodyStatement mbs) {
        HashSet result = new HashSet();
        for (int i = 0; i < mbs.getArguments().size(); i++) {
            result.add(mbs.getArguments().getExpression(i));
        }
        return result;
    }

    public Sequent getPrecondition() {
        return precondition;
    }

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

    public SourceElementId getProgramCounter(PosInOccurrence pio) {
        final JavaBlock jb = modalityTopLevel(pio);
        if (jb != null) {
            return this.getProgramCounter(jb);
        }
        return null;

    }

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

    public int getRunLimit() {
        return runLimit;
    }

    public ProgramVariable getSelfPV() {
        return selfPV;
    }

    public Term getSelfTerm() {
        return TermFactory.DEFAULT.createVariableTerm(selfPV);
    }

    public SetOfTerm getSymbolicInputValues() {
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        for (Iterator it = this.term2InputPV.keySet().iterator(); it.hasNext();) {
            result = result.add((Term) it.next());
        }
        return result;

    }

    public ListOfTerm getSymbolicInputValuesAsList() {
        return this.symbolicInputValuesAsList;
    }

    // public StatementId getStatementId(SourceElement se){
    // return null;
    // }

    // private boolean contains(Node n1,
    // Node n2) {

    // if (getMethodStackSize(t) >= getMethodStackSize(p2)) {
    // per definition a statement does not contain itself
    // if (pcte.getSrcElement().getPositionInfo().equals(
    // cte.getSrcElement().getPositionInfo())) {
    // return false;
    // }

    // final StatementByPositionWalker walker =
    // new StatementByPositionWalker(
    // (ProgramElement) pcte.getSrcElement(), cte.getSrcElement()
    // .getPositionInfo());
    // walker.start();

    // return walker.getResult() != null;
    // }

    // return true;
    // }

    public HashMap getTerm2InputPV() {
        return term2InputPV;
    }

    public ClassType getType() {
        return type;
    }

    /**
     * @param locs
     *            set of Terms (ops)
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

    public void initialize() {

        UpdateLabelListener lListener = new UpdateLabelListener();
        // lListener.setListeners(listeners);
        Goal.addRuleAppListener(lListener);
        mediator.setMaxAutomaticSteps(20000);
        mediator.getProof().setActiveStrategy(
                DebuggerStrategy.Factory.create(mediator.getProof(),
                        "DebuggerStrategy", null));
        // ip.getProof().getGoal((ip.getProof().root())).addRuleAppListener((new
        // de.uka.ilkd.key.visualdebugger.UpdateLabelListener());
        // ..addRuleAppListener);

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

        ExecutionTree pl = new ExecutionTree(mediator.getProof(), mediator,
                true);
        pl.setListeners(listeners);
        mediator.addAutoModeListener(pl);

        this.initPhase = true;
        bpManager.setNoEx(true);
        run();

        // ListOfGoal goals = ip.getProof().openGoals();

    }

    public boolean isDeterminePostValue() {
        return determinePostValue;
    }

    public boolean isInitPhase() {
        return initPhase;
    }

    public boolean isSepStatement(ProgramElement pe) {
        if (pe instanceof MethodReference) {
            MethodReference mr = (MethodReference) pe;
            if (mr.getMethodName().toString().equals(sepName))
                return true;

        }
        return false;

    }

    public boolean isStaticMethod() {
        return staticMethod;
    }

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

    public String prettyPrint(SetOfTerm l, LinkedList objects,
            SymbolicObject thisObject) {
        return prettyPrint(SLListOfTerm.EMPTY_LIST.append(l.toArray()),
                objects, thisObject);
    }

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

    public String prettyPrint(Term l, LinkedList sos, SymbolicObject so) {
        // KeYMediator mediator=
        // VisualDebugger.getVisualDebugger().getMediator();
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

    public void printTestCases() {
        print(this.tc2node.toString());
    }

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

    public ListOfTerm removeImplicite(ListOfTerm list) {
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;

        for (IteratorOfTerm it = list.iterator(); it.hasNext();) {
            final Term n = it.next();
            if (!VisualDebugger.containsImplicitAttr(n))
                result = result.append(n);

        }
        return result;
    }

    private String removeLineBreaks(String s) {
        return s.replace('\n', ' ');
    }

    private void removeStepOver(ListOfGoal goals) {
        IteratorOfGoal it = goals.iterator();
        while (it.hasNext()) {
            Node next = it.next().node();
            next.getNodeInfo().getVisualDebuggerState().setStepOver(-1);
            next.getNodeInfo().getVisualDebuggerState().setStepOverFrom(-1);
            print("StepOver of " + next.serialNr() + " set to -1");
        }

    }

    public boolean run() {
        // this.refreshRuleApps();
        if (!mediator.autoMode()) {
            run(mediator.getProof().openGoals());
            return true;
        } else
            return false;
    }

    public boolean run(ListOfGoal goals) {
        if (!mediator.autoMode()) {
            this.removeStepOver(goals);
            this.setSteps(goals, this.runLimit);

            runProver(goals);
            return true;

        }
        return false;
    }

    // public void setRunLimit(int runLimit) {
    // this.runLimit = runLimit;
    // }

    private void runProver(final ListOfGoal goals) {
        this.refreshRuleApps();
        mediator.startAutoMode(goals);
    }

    public void setDeterminePostValue(boolean determinePostValue) {
        this.determinePostValue = determinePostValue;
    }

    public void setInitPhase(boolean initPhase) {
        this.initPhase = initPhase;
    }

    public void setInputPV2term(HashMap inputPV2term) {
        this.inputPV2term = inputPV2term;
    }

    public void setSelfPV(ProgramVariable selfPV) {
        this.selfPV = selfPV;
    }

    public void setStaticMethod(boolean staticMethod) {
        this.staticMethod = staticMethod;
    }

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

    public void setTerm2InputPV(HashMap inputValues) {
        this.term2InputPV = inputValues;
    }

    public void setType(ClassType type) {
        this.type = type;
    }

    public ListOfTerm simplify(ListOfTerm terms) {
        if (terms.size() == 0)
            return terms;
        DebuggerPO po = new DebuggerPO("DebuggerPo");
        ProofStarter ps = new ProofStarter();
        po.setTerms(terms);
        po.setIndices(mediator.getProof().env().getInitConfig()
                .createTacletIndex(), mediator.getProof().env().getInitConfig()
                .createBuiltInRuleIndex());
        po.setProofSettings(mediator.getProof().getSettings());
        po.setConfig(mediator.getProof().env().getInitConfig());
        po.setTerms(terms);
        ps.init(po);
        InUpdateFeature.splitting_rules = false;
        ps.getProof().setActiveStrategy(
                (DebuggerStrategy.Factory.create(ps.getProof(),
                        "DebuggerStrategy", null)));
        ps.run(mediator.getProof().env());
        InUpdateFeature.splitting_rules = true;
        ps.getProof().openGoals().iterator().next().node().sequent();
        return collectResult(ps.getProof().openGoals().iterator().next().node()
                .sequent());
    }

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

    public boolean stepInto() {
        return stepInto(mediator.getProof().openGoals());
    }

    public boolean stepInto(ListOfGoal goals) {
        return this.stepInto(goals, 1);
    }

    public boolean stepInto(ListOfGoal goals, int steps) {
        if (!mediator.autoMode()) {
            removeStepOver(mediator.getProof().openGoals());
            this.setSteps(goals, steps);
            runProver(goals);
            return true;
        }
        return false;
    }

    public void stepOver() {
        this.stepOver(mediator.getProof().openGoals());
    }

    public void stepOver(ListOfGoal goals) {
        setStepOver(goals);
        this.setSteps(goals, runLimit);
        runProver(goals);
    }

    public boolean stepToFirstSep() {
        if (!mediator.autoMode()) {

            removeStepOver(mediator.getProof().openGoals());
            setSteps(mediator.getProof().openGoals(), 0);
            runProver(mediator.getProof().openGoals());
            return true;
        }
        return false;
    }

    public synchronized void visualize(ITNode n) {
        mediator = main.mediator();
        final ITNode node = n;

        final Runnable interfaceSignaller = new Runnable() {
            public void run() {
                new StateVisualization(node, mediator);

            }
        };

        startThread(interfaceSignaller);
    }

    public class TestCaseIdentifier {

        private final String file;

        private final String method;

        public TestCaseIdentifier(String file, String method) {
            this.file = file;
            this.method = method;
        }

        public boolean equals(Object o) {
            if (o instanceof TestCaseIdentifier) {
                TestCaseIdentifier tci = (TestCaseIdentifier) o;
                return file.equals(tci.getFile())
                        && method.equals(tci.getMethod());
            }

            return false;
        }

        public String getFile() {
            return file;
        }

        public String getMethod() {
            return method;
        }

        public int hashCode() {
            return (method.concat(file)).hashCode();
        }

        public String toString() {
            return "File: " + file + " Method: " + method;
        }

    }
}