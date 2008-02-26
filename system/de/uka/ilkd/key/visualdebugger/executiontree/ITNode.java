package de.uka.ilkd.key.visualdebugger.executiontree;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.ArrayOfParameterDeclaration;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProgVarReplacer;
import de.uka.ilkd.key.rule.ListOfRuleSet;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.ContextInstantiationEntry;
import de.uka.ilkd.key.visualdebugger.SourceElementId;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

public class ITNode {
    private SourceElement activeStatement;

    ListOfTerm bc = SLListOfTerm.EMPTY_LIST;

    private LinkedList<ITNode> children = new LinkedList<ITNode>();

    private boolean exprEnd;

    private ProgramVariable expressionResultVar = null;

    private SourceElementId exprId = null;

    private final int id;

    private HashSet idsOfNonPVExpressions = new HashSet();

    private boolean isMethodInvokation = false;

    private ITNode lastExpressionId;

    private boolean methodInvocationForET;

    private ITNode methodNode;

    private Term methodReference;

    private boolean methodReturn;

    private Term methodReturnResult;

    private boolean nobc = false;

    private final Node node;

    private ListOfProgramVariable parameter;

    private final ITNode parent;

    ListOfTerm pc = SLListOfTerm.EMPTY_LIST;

    private ProgramMethod programMethod;

    private Services serv = null;

    private SourceElementId statementId = null;

    private ListOfTerm values = null;

    private VisualDebugger vd = VisualDebugger.getVisualDebugger();

    public ITNode(ListOfTerm bc, ListOfTerm pc, Node n, ITNode parent) {
        this.bc = bc;
        this.parent = parent;
        this.serv = n.proof().getServices();
        this.id = n.serialNr();
        this.pc = pc;
        this.node = n;
        if (parent != null)
            this.idsOfNonPVExpressions = (HashSet) parent.idsOfNonPVExpressions
                    .clone();
        this.activeStatement = calcActStatement();
        statementId = calcStatementId();
        this.exprId = calcExprId();
        this.exprEnd = calcExprEnd();
        this.methodReturn = calcMethodReturn();
        this.isMethodInvokation = this.calcIsMethodInvocation();
        setMethodNode();
    }

    public ITNode(Node n) {
        
        this.serv = n.proof().getServices();
        this.parent = null;
        this.id = n.serialNr();
        this.node = n;
        this.methodNode = null;
        this.activeStatement = calcActStatement();
        this.statementId = calcStatementId();
        this.exprEnd = calcExprEnd();
        this.exprId = calcExprId();
        this.isMethodInvokation = this.calcIsMethodInvocation();
    }

    public void addChild(ITNode n) {
        children.add(n);
    }

    private SourceElement calcActStatement() {
        return vd.determineFirstAndActiveStatement(node);

    }

    private boolean calcExprEnd() {

        if (activeStatement instanceof MethodBodyStatement) {
            final MethodBodyStatement mbs = (MethodBodyStatement) activeStatement;
            // FIXME: do not lookup for method using Strings use the real AST
            // objects instead
            // This is likely to break as soon as a method ending with sep is
            // present
            if (mbs.getMethodReference().getMethodName().toString().endsWith(
                    "sep")) {
                if (mbs.getArguments().size() > 1) { // is expression sep, no
                    // statment sep
                    this.expressionResultVar = (ProgramVariable) mbs
                            .getArguments().getExpression(1);

                    return true;
                }

            }
        }

        // FIXME: What happens here?
        if (true)
            return false;

        if (activeStatement != null
                && node.getAppliedRuleApp() instanceof PosTacletApp) {
            PosTacletApp pta = (PosTacletApp) node.getAppliedRuleApp();

            MethodFrame mf = getMethodFrame(pta);
            if (mf == null || mf.getProgramMethod() == null)
                return false;

            if (mf.getProgramMethod().name().toString().endsWith("sep") // TODO
                    // remove
                    // taclet
                    // names...
                    // with
                    // special
                    // tacltes
                    // for
                    // sep,
                    // eg.
                    && node.getAppliedRuleApp().rule().displayName().toString()
                            .equals("method_call_return"))
                return true;
        }
        return false;
    }

    /**
     * active statement of the form int b = sep(12,expr);
     * 
     * @return
     */
    private SourceElementId calcExprId() {
        if (parent != null && parent.getExprId() != null)
            this.lastExpressionId = parent;
        else if (isExprEnd())
            lastExpressionId = parent.getLastExpressionId()
                    .getLastExpressionId();
        else if (parent != null)
            lastExpressionId = parent.getLastExpressionId();
        else
            this.lastExpressionId = null;

        final SourceElement statement = activeStatement;

        if (statement != null && statement instanceof CopyAssignment) {

            final SourceElement act = ((Assignment) statement).getChildAt(1);

            if (act != null && act instanceof MethodReference) {
                MethodReference mr = (MethodReference) act;
                // FIXME: do not lookup for method using Strings use the real
                // AST objects instead
                // This is likely to break.
                if (mr.getMethodName().toString().equals("sep")
                        && mr.getArgumentAt(0) instanceof IntLiteral) {// TODO
                    // sep(11,expr)

                    if (node.getAppliedRuleApp() instanceof PosTacletApp) {

                        final ProgramVariable pv = (ProgramVariable) ((Assignment) statement)
                                .getChildAt(0);

                        PosTacletApp pta = (PosTacletApp) node
                                .getAppliedRuleApp();
                        MethodFrame mf = getMethodFrame(pta);
                        ExecutionContext ec = (ExecutionContext) mf
                                .getExecutionContext();
                        final SourceElementId sid = new SourceElementId(
                                ec.getTypeReference().toString(),
                                ((IntLiteral) (mr.getArgumentAt(0))).getValue(),
                                false,
                                pv.getKeYJavaType().getJavaType() == PrimitiveType.JAVA_BOOLEAN);

                        if (!isTempVar(mr.getArgumentAt(1), sid))

                            return sid;
                    }

                }

            }
        }
        return null;
    }

    private boolean calcIsMethodInvocation() {
        if (node.getAppliedRuleApp() != null
                && node.getAppliedRuleApp().rule().name().toString().equals(
                        "introduce_post_predicate"))
            return false;

        if (activeStatement instanceof MethodBodyStatement) {
            final MethodBodyStatement mbs = (MethodBodyStatement) activeStatement;
            final String name = mbs.getMethodReference().getMethodName()
                    .toString();
            // FIXME: do no use Strings to identify these methods
            if (name.startsWith("<alloc") || name.endsWith("sep")) {
                return false; // no element added to method stack
            }
            this.methodInvocationForET = true;

            if (this.inExecutionTree(mbs))
                this.methodInvocationForET = true;
            else
                this.methodInvocationForET = false;

            ReferencePrefix refPre = mbs.getMethodReference()
                    .getReferencePrefix();

            if (refPre instanceof TypeRef) {
                final KeYJavaType kjt = ((TypeRef) refPre).getKeYJavaType();
                final ClassType type = (ClassType) kjt.getJavaType();
                // so = getStaticObject(type, symbolicObjects);

                programMethod = (mbs.getProgramMethod(serv));

            } else {

                final Term t = serv.getTypeConverter().convertToLogicElement(
                        refPre);
                methodReference = t;
                HashMap map = new HashMap();
                Term baseVar = getPref(t);

                PosInOccurrence pio = vd.getProgramPIO(getNode().sequent());
                HashSet set = new HashSet();
                set.add(baseVar.op());
                HashMap result = vd.getValuesForLocation(set, pio);
                Term val = (Term) result.get(TermFactory.DEFAULT
                        .createVariableTerm((ProgramVariable) baseVar.op()));
                map.put(baseVar.op(), val);
                ProgVarReplacer pvr = new ProgVarReplacer(map, serv);
                Term res = pvr.replace(t);
                programMethod = mbs.getProgramMethod(serv);

                methodReference = res;
            }

            HashSet set = vd.getParam(mbs);
            ListOfProgramVariable inputPara = vd
                    .arrayOfExpression2ListOfProgVar(mbs.getArguments(), 0);
            ProgramVariable[] inputParaArray = inputPara.toArray();

            ArrayOfParameterDeclaration paraDecl = mbs.getProgramMethod(serv)
                    .getParameters();
            final HashMap loc2val = vd.getValuesForLocation(set, vd
                    .getProgramPIO(node.sequent()));

            ListOfProgramVariable paramDeclAsPVList = SLListOfProgramVariable.EMPTY_LIST;

            this.values = SLListOfTerm.EMPTY_LIST;

            for (int i = 0; i < paraDecl.size(); i++) {
                ProgramVariable next = (ProgramVariable) paraDecl
                        .getParameterDeclaration(i).getVariableSpecification()
                        .getProgramVariable();
                Term val = (Term) loc2val.get(TermFactory.DEFAULT
                        .createVariableTerm(inputParaArray[i]));// TODO
                this.values = this.values.append(val);
                paramDeclAsPVList = paramDeclAsPVList.append(next);

            }
            parameter = (paramDeclAsPVList);

            return true;

        }

        return false;

    }

    /**
     * The method computes if this node represents a method return node, i.e. if
     * it describes a state exactly after a method has returned. This is the
     * case iff. the parent's node method stack has at least a depth of
     * <tt>1</tt> (it must be inside a method) and the difference between the
     * method stack depths is exactly once and the reason for the decrease is
     * not a thrown exception.
     * 
     * @return true if this node represent the state after a normal method
     *         return
     */
    private boolean calcMethodReturn() {
        if (parent == null) {
            return false;
        }

        final int stackSize1 = vd.getMethodStackSize(parent.node);
        final int stackSize2 = vd.getMethodStackSize(node);

        if (stackSize1 <= 0) {
            return false;
        }

        if (this.activeStatement instanceof Throw) {
            return false;
        }

        return (stackSize1 - stackSize2) == 1;
    }

    private synchronized SourceElementId calcStatementId() {
        if (node.getAppliedRuleApp() != null
                && node.getAppliedRuleApp().rule() != null
                && node.getAppliedRuleApp().rule() instanceof Taclet) {
            Taclet taclet = (Taclet) node.getAppliedRuleApp().rule();
            if (!this.tacletIsInRuleSet(taclet, "statement_sep"))
                return null;

        } else
            return null;

        SourceElement act = this.activeStatement;
        if (act != null && act instanceof MethodReference) {
            MethodReference mr = (MethodReference) act;
            if (mr.getMethodName().toString().equals(VisualDebugger.sepName)
                    && mr.getArgumentAt(0) instanceof IntLiteral) {
                if (node.getAppliedRuleApp() != null
                        && node.getAppliedRuleApp().rule() != null
                        && !node.getAppliedRuleApp().rule().name().toString()
                                .equals("introduce_post_predicate")) {
                    if (node.getAppliedRuleApp() instanceof PosTacletApp) {

                        PosTacletApp pta = (PosTacletApp) node
                                .getAppliedRuleApp();
                        MethodFrame mf = getMethodFrame(pta);
                        ExecutionContext ec = (ExecutionContext) mf
                                .getExecutionContext();

                        return new SourceElementId(ec.getTypeReference()
                                .toString(),
                                ((IntLiteral) (mr.getArgumentAt(0))).getValue());
                    }
                }
            }

        }

        return null;
    }

    public SourceElement getActStatement() {

        return activeStatement;
    }

    public ListOfTerm getBc() {
        return bc;
    }

    public ITNode[] getChildren() {
        return (ITNode[]) children.toArray(new ITNode[children.size()]);
    }

    public ProgramVariable getExpressionResultVar() {
        return expressionResultVar;
    }

    public SourceElementId getExprId() {
        return exprId;
    }

    public int getId() {
        return id;
    }

    public ITNode getLastExpressionId() {
        return lastExpressionId;
    }

    private MethodFrame getMethodFrame(PosTacletApp pta) {
        final ContextInstantiationEntry cie = pta.instantiations()
                .getContextInstantiation();
        if (cie == null)
            return null;
        else
            return vd.getMethodFrame(cie.contextProgram());

    }

    public ITNode getMethodNode() {
        return methodNode;
    }

    public Term getMethodReference() {
        return methodReference;
    }

    public Term getMethodReturnResult() {
        return methodReturnResult;
    }

    public Node getNode() {
        return node;
    }

    public ListOfProgramVariable getParameter() {
        return parameter;
    }

    public ITNode getParent() {
        return parent;
    }

    public ListOfTerm getPc() {
        // remove implicit
        if (!VisualDebugger.showImpliciteAttr)
            return vd.removeImplicite(pc);
        return pc;
    }

    public ListOfTerm getPc(boolean impl) {
        // remove implicit
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;

        for (IteratorOfTerm it = pc.iterator(); it.hasNext();) {
            final Term n = it.next();
            if (!VisualDebugger.containsImplicitAttr(n) || impl)
                result = result.append(n);

        }

        return result;
    }

    private Term getPref(Term t) {
        while (t.op() instanceof AttributeOp) {
            t = t.sub(0);

        }

        // TODO Auto-generated method stub
        return t;
    }

    public ProgramMethod getProgramMethod() {
        return programMethod;
    }

    public SourceElementId getStatementId() {
        return statementId;
    }

    public ListOfTerm getValues() {
        return values;
    }

    public boolean inExecutionTree(MethodBodyStatement mbs) {
        final String name = mbs.getMethodReference().getMethodName().toString();
        String className = mbs.getProgramMethod(serv).getContainerType()
                .getSort().toString();
        if (className.startsWith("java") || className.startsWith("System"))
            return false;

        if (!name.startsWith("<") || name.startsWith("<init>"))
            return true;

        return false;
    }

    public boolean isExprEnd() {
        return this.exprEnd;
    }

    public boolean isMethodInvocation() {
        return isMethodInvokation;
    }

    public boolean isMethodInvocationForET() {
        return methodInvocationForET;
    }

    public boolean isMethodReturn() {
        return methodReturn;
    }

    public boolean isNobc() {
        return nobc;
    }

    private boolean isTempVar(Expression e, SourceElementId id) {
        if (e instanceof ProgramVariable) {
            if (this.idsOfNonPVExpressions.contains(id))
                return true;
        } else {
            this.idsOfNonPVExpressions.add(id);
        }

        return false;
    }

    public void removeAllChildren() {
        this.children = new LinkedList();
    }

    private void setMethodNode() {
        if (parent.isMethodInvocation()) {
            this.methodNode = parent;
        } else if (methodReturn) {
            if (parent.getMethodNode() != null) {
                // compute return value
                methodNode = parent.getMethodNode().getMethodNode();
                MethodBodyStatement mbs = (MethodBodyStatement) parent
                        .getMethodNode().getActStatement();
                IProgramVariable resultVar = mbs.getResultVariable();
                if (resultVar != null) {
                    final PosInOccurrence pio = vd.getProgramPIO(getNode()
                            .sequent());
                    HashSet set = new HashSet();
                    set.add(resultVar);
                    final HashMap result = vd.getValuesForLocation(set, pio);
                    // TODO
                    this.methodReturnResult = (Term) result
                            .get(TermFactory.DEFAULT
                                    .createVariableTerm((ProgramVariable) resultVar));
                }
            }
        } else {
            this.methodNode = parent.getMethodNode();
        }
    }

    public void setNobc(boolean nobc) {
        this.nobc = nobc;
    }

    private boolean tacletIsInRuleSet(Taclet t, String ruleSet) {
        ListOfRuleSet list = t.getRuleSets();
        RuleSet rs;
        while (!list.isEmpty()) {
            rs = list.head();
            Name name = rs.name();
            if (name.toString().equals(ruleSet))
                return true;
            list = list.tail();
        }
        return false;
    }

    public String toString() {
        String result = "";
        result = result + " (( " + bc + " Node " + id + " ";
        Iterator it = children.iterator();
        while (it.hasNext()) {
            result = result + it.next();
        }

        result = result + " ))";

        return result;
    }

}
