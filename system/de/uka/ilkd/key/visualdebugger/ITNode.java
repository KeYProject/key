package de.uka.ilkd.key.visualdebugger;

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

public class ITNode {
    private LinkedList children = new LinkedList();

    private SourceElement activeStatement;

    ListOfTerm bc= SLListOfTerm.EMPTY_LIST;

    ListOfTerm pc = SLListOfTerm.EMPTY_LIST;

    private boolean exprEnd;

    private final ITNode parent;

    private final Node node;

    private boolean nobc=false;

    private ProgramVariable expressionResultVar=null;

    private boolean methodReturn;

    private Term methodReturnResult;

    private boolean isMethodInvokation=false;

    private VisualDebugger vd = VisualDebugger.getVisualDebugger();

    private Services serv = VisualDebugger.getVisualDebugger().getMediator().getServices();

    private HashSet idsOfNonPVExpressions = new HashSet();

    private final int id;

    private SourceElementId statementId = null;

    private SourceElementId exprId = null;

    private Term methodReference;

    private ProgramMethod programMethod;

    private ListOfProgramVariable parameter;

    private ListOfTerm values = null;

    private  ITNode methodNode;

    private boolean methodInvocationForET;

    private ITNode lastExpressionId;

    public ITNode(ListOfTerm bc, ListOfTerm pc, Node n,ITNode parent) {        
        this.bc = bc;
        this.parent=parent;

        this.id = n.serialNr();
        this.pc = pc;
        this.node = n;       
        if (parent!=null)
            this.idsOfNonPVExpressions=(HashSet)parent.idsOfNonPVExpressions.clone();
        this.activeStatement = calcActStatement();
        statementId = calcStatementId();
        this.exprId = calcExprId();
        this.exprEnd = calcExprEnd();
        this.methodReturn = calcMethodReturn();
        this.isMethodInvokation = this.calcIsMethodInvocation();
        setMethodNode();
    }
    
    public ITNode(Node n) {
        this.parent = null;
        this.id = n.serialNr();
        this.node = n;
        this.methodNode=null;
        this.activeStatement = calcActStatement();        
        this.statementId = calcStatementId();
        this.exprEnd = calcExprEnd();
        this.exprId = calcExprId();
        this.isMethodInvokation = this.calcIsMethodInvocation();
    }

    private void setMethodNode() {
        if (parent.isMethodInvocation()){
            this.methodNode = parent;
        } else if (methodReturn) {
            if (parent.getMethodNode()!=null){
                //compute return value
                methodNode = parent.getMethodNode().getMethodNode();
                MethodBodyStatement mbs =(MethodBodyStatement)
                parent.getMethodNode().getActStatement();
                IProgramVariable resultVar =mbs.getResultVariable();
                if(resultVar!=null){
                    final PosInOccurrence pio =vd.getProgramPIO(getNode().sequent());                    
                    HashSet set = new HashSet();
                    set.add(resultVar);
                    final HashMap result = vd.getValuesForLocation(set, pio);
                    //TODO
                    this.methodReturnResult = (Term)result.get(TermFactory.DEFAULT.createVariableTerm((ProgramVariable)resultVar));
                }
            }
        } else {
            this.methodNode=parent.getMethodNode();
        }        
    }


    private boolean calcMethodReturn() {
        if (parent == null) {
            return false;    
        }
        int stackSize1 = vd.getMethodStackSize(parent.node);
        int stackSize2 = vd.getMethodStackSize(node);

        if (stackSize2 < 0) {
            return false;
        }
        
        if (this.activeStatement instanceof Throw) {
            return false;
        }
        return stackSize2<stackSize1;
    }


   

    public ITNode getParent(){
        return parent;
    }

    public void addChild(ITNode n) {
        children.add(n);
    }

    public ListOfTerm getBc() {     
        return bc;
    }


    public boolean isExprEnd(){
        return this.exprEnd;
    }

    public ListOfTerm getPc() {
        //remove implicit
        if (!VisualDebugger.showImpliciteAttr)
            return vd.removeImplicite(pc);
        return pc;
    }

    public ListOfTerm getPc(boolean impl) {
        //remove implicit
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;

        for(IteratorOfTerm it= pc.iterator();it.hasNext();){
            final Term n = it.next();
            if (!VisualDebugger.containsImplicitAttr(n) || impl)
                result = result.append(n);

        }

        return result;
    }

    public ITNode[] getChildren() {
        return (ITNode[]) children.toArray(new ITNode[children.size()]);
    }

    public int getId() {
        return id;
    }

    public void removeAllChildren(){
        this.children = new LinkedList();
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

    private SourceElement calcActStatement() {
        return vd.determineFirstAndActiveStatement(node);

    }


    private boolean tacletIsInRuleSet(Taclet t,String ruleSet) {
        ListOfRuleSet list = t.getRuleSets();
        RuleSet       rs;
        while (!list.isEmpty()) {
            rs = list.head ();
            Name name = rs.name();
            if (name.toString().equals(ruleSet)) return true;
            list = list.tail();
        }
        return false;
    }

    public boolean inExecutionTree(MethodBodyStatement mbs){
        final String name = mbs.getMethodReference().getMethodName().toString();
        String className = mbs.getProgramMethod(serv).getContainerType().getSort().toString();
        if (className.startsWith("java")
                || className.startsWith("System"))
            return false;

        if (!name.startsWith("<")|| name.startsWith("<init>"))
            return true;


        return false;
    }

    private boolean calcIsMethodInvocation() {
        if (node.getAppliedRuleApp()!=null && node.getAppliedRuleApp().rule().name().toString()
                .equals("introduce_post_predicate"))
            return false;

        if (activeStatement instanceof MethodBodyStatement){
            final MethodBodyStatement mbs = (MethodBodyStatement)activeStatement;
            final String name = mbs.getMethodReference().getMethodName().toString();
            if (name.startsWith("<alloc")|| name.endsWith("sep")) {
                return false; //no element added to method stack
            }
            this.methodInvocationForET = true;

            if (this.inExecutionTree(mbs))
                this.methodInvocationForET=true;
            else  this.methodInvocationForET=false;

            ReferencePrefix refPre = mbs.getMethodReference().getReferencePrefix(); 

            if (refPre instanceof TypeRef){
                final KeYJavaType kjt = ((TypeRef)refPre).getKeYJavaType();
                final ClassType type = (ClassType)kjt.getJavaType();
                //so = getStaticObject(type, symbolicObjects);

                programMethod = (mbs.getProgramMethod(serv));

            }else{

                final Term t = serv.getTypeConverter().convertToLogicElement(refPre);
                methodReference = t;
                HashMap map = new HashMap();
                Term baseVar = getPref(t);

                PosInOccurrence pio =vd.getProgramPIO(getNode().sequent());
                HashSet set = new HashSet();
                set.add(baseVar.op());
                HashMap result = vd.getValuesForLocation(set, pio);
                Term val = (Term)result.get(TermFactory.DEFAULT.createVariableTerm((ProgramVariable)baseVar.op()));
                map.put(baseVar.op(), val);
                ProgVarReplacer pvr = new ProgVarReplacer(serv, map);
                Term res = pvr.replace(t);
                programMethod = mbs.getProgramMethod(serv);


                methodReference = res;
            }

            HashSet set = vd.getParam(mbs);
            ListOfProgramVariable inputPara = vd.arrayOfExpression2ListOfProgVar(mbs.getArguments(),0);
            ProgramVariable[] inputParaArray = inputPara.toArray();

            ArrayOfParameterDeclaration paraDecl = mbs.getProgramMethod(serv).getParameters();
            final HashMap loc2val = vd.getValuesForLocation(set, vd.getProgramPIO(node.sequent()));        


            ListOfProgramVariable paramDeclAsPVList= SLListOfProgramVariable.EMPTY_LIST;

            this.values = SLListOfTerm.EMPTY_LIST;

            for(int i=0;i<paraDecl.size();i++){
                ProgramVariable next = (ProgramVariable)paraDecl.getParameterDeclaration(i).getVariableSpecification().getProgramVariable();
                Term val = (Term) loc2val.get(TermFactory.DEFAULT.createVariableTerm(inputParaArray[i]));//TODO
                this.values = this.values.append(val);
                paramDeclAsPVList =paramDeclAsPVList.append(next); 



            }
            parameter = (paramDeclAsPVList);

            return true;


        } 

        return false;

    }



    private Term getPref(Term t) {
        while(t.op() instanceof AttributeOp){
            t = t.sub(0);

        }

        // TODO Auto-generated method stub
        return t;
    }


    /** active statement of the form  int b = sep(12,expr);
     * 
     * @return
     */

    private SourceElementId calcExprId(){
        if(parent!=null && parent.getExprId()!=null)
            this.lastExpressionId=parent;
        else if (isExprEnd())
            lastExpressionId =parent.getLastExpressionId().getLastExpressionId();
        else if (parent!=null )lastExpressionId= parent.getLastExpressionId();
        else this.lastExpressionId=null;


        final SourceElement statement = activeStatement;

        if (statement!=null && statement instanceof CopyAssignment){

            final SourceElement act =  ((Assignment)statement).getChildAt(1);

            if (act != null && act instanceof MethodReference) {
                MethodReference mr = (MethodReference) act;


                if (mr.getMethodName().toString().equals("sep")
                        && mr.getArgumentAt(0) instanceof IntLiteral
                ) {//TODO sep(11,expr)

                    if (node.getAppliedRuleApp() instanceof PosTacletApp) {

                        final ProgramVariable pv = (ProgramVariable)((Assignment)statement).getChildAt(0);

                        PosTacletApp pta = (PosTacletApp) node.getAppliedRuleApp();
                        MethodFrame mf = getMethodFrame(pta);
                        ExecutionContext ec = (ExecutionContext) mf
                        .getExecutionContext();
                        final SourceElementId sid = new SourceElementId(
                                ec.getTypeReference().toString(),
                                ((IntLiteral) (mr.getArgumentAt(0))).getValue(),false,
                                pv.getKeYJavaType().getJavaType()==PrimitiveType.JAVA_BOOLEAN)
                        ;

                        if (!isTempVar(mr.getArgumentAt(1),sid))    

                            return  sid;
                    }

                }

            }
        }
        return null;
    }



    private boolean isTempVar(Expression e,SourceElementId id) {
        if (e instanceof ProgramVariable){
            if (this.idsOfNonPVExpressions.contains(id))
                return true;
        }else{
            this.idsOfNonPVExpressions.add(id);
        }


        return false;
    }


    private boolean calcExprEnd() {  

        if (activeStatement instanceof MethodBodyStatement){
            final MethodBodyStatement mbs = (MethodBodyStatement)activeStatement;
            if (mbs.getMethodReference().getMethodName().toString().endsWith("sep")){
                if (mbs.getArguments().size()>1){   //is expression sep, no statment sep
                    this.expressionResultVar= (ProgramVariable)mbs.getArguments().getExpression(1);

                    return true;
                }

            }
        }


        if (true)
            return false;

        if (activeStatement!=null && node.getAppliedRuleApp() instanceof PosTacletApp) {
            PosTacletApp pta = (PosTacletApp) node.getAppliedRuleApp();

            MethodFrame mf = getMethodFrame(pta);
            if (mf==null||mf.getProgramMethod()==null)
                return false;

            if (mf.getProgramMethod().name().toString().endsWith("sep") //TODO remove taclet names... with special tacltes for sep, eg.
                    && node.getAppliedRuleApp().rule().displayName().toString().equals("method_call_return"))
                return true;
        }
        return false;
    }


    public SourceElement getActStatement() {

        return activeStatement;
    }

    private synchronized SourceElementId calcStatementId() {
        if ( node.getAppliedRuleApp() != null
                && node.getAppliedRuleApp().rule() != null &&
                node.getAppliedRuleApp().rule() instanceof Taclet){
            Taclet taclet = (Taclet) node.getAppliedRuleApp().rule();
            if (!this.tacletIsInRuleSet(taclet, "statement_sep"))
                return null;

        } else return null;


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

                        PosTacletApp pta = (PosTacletApp) node.getAppliedRuleApp();
                        MethodFrame mf = getMethodFrame(pta);
                        ExecutionContext ec = (ExecutionContext) mf
                        .getExecutionContext();

                        return new SourceElementId(
                                ec.getTypeReference().toString(),
                                ((IntLiteral) (mr.getArgumentAt(0))).getValue());
                    }
                }
            }

        }

        return null;
    }

    public SourceElementId getStatementId() {
        return statementId;
    }


    public SourceElementId getExprId() {
        return exprId;
    }


    private MethodFrame getMethodFrame(PosTacletApp pta) {
        final ContextInstantiationEntry cie = pta.instantiations()
        .getContextInstantiation();
        if (cie == null)
            return null;
        else  return vd.getMethodFrame(cie.contextProgram());

    }

    public Node getNode() {
        return node;
    }


    public boolean isNobc() {
        return nobc;
    }


    public void setNobc(boolean nobc) {
        this.nobc = nobc;
    }


    public ProgramVariable getExpressionResultVar() {
        return expressionResultVar;
    }


    public boolean isMethodInvocation() {
        return isMethodInvokation;
    }


    public ListOfProgramVariable getParameter() {
        return parameter;
    }


    public Term getMethodReference() {
        return methodReference;
    }


    public ProgramMethod getProgramMethod() {
        return programMethod;
    }


    public ListOfTerm getValues() {
        return values;
    }


    public ITNode getMethodNode() {
        return methodNode;
    }


    public boolean isMethodInvocationForET() {
        return methodInvocationForET;
    }


    public Term getMethodReturnResult() {
        return methodReturnResult;
    }


    public boolean isMethodReturn() {
        return methodReturn;
    }


    public ITNode getLastExpressionId() {
        return lastExpressionId;
    }




}
