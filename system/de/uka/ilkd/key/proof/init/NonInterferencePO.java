// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import java.util.Enumeration;
import java.util.LinkedList;
import java.util.Vector;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.SynchronizedBlock;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.key.util.KeYExceptionHandler;

/* TODO

synchro:
-(X)convert MetaClassReference to a constant
-skip 1st statement in block

sequent state:
-extend to qualif. attributes and arrays as lvalues

syntactic cond.:
-(X)add a semantic check at "leaf" nodes
-generalize set elements from SV to schematic terms

jmm stuff:
-rename variables
-(-)generalize constants
-volatile variables
*/


public class NonInterferencePO implements ProofOblInput {


    ProofAggregate po;
    InitConfig initConfig;
    Proof proof1,proof2;
    
    ProgramVariable trueSelf;
    
    public NonInterferencePO(ProofEnvironment env, Proof p1, Proof p2) {
        initConfig = env.getInitConfig();
        if(p1 == null || p2 == null)throw new IllegalStateException(
            "Proofs are not initialised");
        proof1 = p1;
        proof2 = p2;
        trueSelf = (ProgramVariable) proof1.getNamespaces().programVariables().
            lookup(new Name("self"));
    }
    
    

    public ProofAggregate getPO() {
        return po;
    }



    public void readProblem(ModStrategy mod) throws ProofInputException {
        Proof p = new Proof( name(), // just a dummy, see createSubgoals()
                             TermFactory.DEFAULT.createJunctorTerm(Op.FALSE),
			     "HOLA!",
			     initConfig.createTacletIndex(),
			     initConfig.createBuiltInRuleIndex(),
			     initConfig.getServices());
    
        po = ProofAggregate.createProofAggregate(new Proof[] { p }, name());
        
    }
    
    
    
    public void createSubgoals() {
        Proof p = po.getFirstProof();
    
        Vector nodes1 = new Vector();
        Vector nodes2 = new Vector();
        getSymExecNodes (proof1.root(),false,nodes1);
        getSymExecNodes (proof2.root(),true, nodes2);
        
        LinkedList conditions = new LinkedList();


        //create the crossproduct of the two lists
        for( Enumeration i=nodes1.elements(); i.hasMoreElements();) {
            Node a = (Node)i.nextElement();
            for( Enumeration j=nodes2.elements(); j.hasMoreElements();) {
                Node b = (Node)j.nextElement();
                if (syntacticNonInterference(a,b)) continue;
                ConstrainedFormula cf = 
                    new ConstrainedFormula(nonInterfCondition(a,b));
                conditions.addFirst(
                    new ConditionContainer(cf,a.serialNr()+"<->"+b.serialNr()));
            }
        }


        Goal firstGoal = p.openGoals().head();
        ListOfGoal newGoals = firstGoal.split(conditions.size());
        de.uka.ilkd.key.proof.IteratorOfGoal it = newGoals.iterator();
        while (it.hasNext()) {
            Goal g = it.next();
            ConditionContainer cc = (ConditionContainer) conditions.getFirst();
            g.addFormula(cc.getFormula(), false, false);
            g.setBranchLabel(cc.getLabel());
            conditions.removeFirst();
        }


        p.replace(firstGoal,newGoals);
    }
    
    
    /** Serves as an utility-method for getPOTerm(). It takes a Node
    (from a proof), traverses the tree of nodes, and collects in v all
    nodes where symbolic execution has been performed. To reduce the
    number of collected elements only nodes with updates will be
    collected if the parameter onlyUpdates is true. */
    private void getSymExecNodes(Node n, boolean onlyUpdates, Vector v) {
        if(v == null) throw new IllegalStateException(
            "The second parameter of getSMNodes is not initialised");
        if(n == null) return;
        if(n.getNodeInfo().getActiveStatement()!=null) {
        /*This is the case if symbolic modification has been performed*/
            if(onlyUpdates) {
             String ruleName = n.getAppliedRuleApp().rule().name().toString();
             if(ruleName.startsWith("assignment_"))
                v.add(n);
            } else {
            v.add(n);
            }
        }
        for(IteratorOfNode ni=n.childrenIterator();ni.hasNext();) {
            getSymExecNodes (ni.next(), onlyUpdates, v);
        }
    }

/**
Serves the getPOTerm() method.
@param a gamma1,gamma2,..., gammaN => <p1> phi
@param b delta1,delta2,..., deltaM => <p2> psi
@return gamma1,gamma2,...,gammaN,delta1,delta2,...,deltaM => <p2'> gamma1,gamma2,...,gammaN
where p2' is the first assignment statement of p2.
*/
    private Term nonInterfCondition(Node a, Node b) {
        Sequent sa = a.sequent();
        Sequent sb = b.sequent();


        Term stateA = sequentState(sa);
        Term resAnte = TermFactory.DEFAULT.createJunctorTerm(Op.AND, 
            stateA, sequentState(sb));

        JavaProgramElement progA = program(sa);
        JavaProgramElement progB = program(sb);

        Term sc = syncCondition(progA,progB);
        if (sc != null) {
            resAnte = TermFactory.DEFAULT.createJunctorTerm(Op.AND,resAnte, sc);
        }


        FirstStatementExtractionVisitor v = 
            new FirstStatementExtractionVisitor(progB, 
                                                b, 
                                                initConfig.getServices());
        v.start();
        JavaBlock p2prime = JavaBlock.createJavaBlock(
            (StatementBlock)v.result());
        Term resSucc = TermFactory.DEFAULT.createBoxTerm(p2prime,stateA);

        return TermFactory.DEFAULT.createJunctorTerm(Op.IMP, resAnte, resSucc);
    }



    private JavaProgramElement program(Sequent s) {
        Term formula = s.succedent().getFirst().formula();
        while (formula.op() instanceof IUpdateOperator)  {
            // skip update
            formula = ( (IUpdateOperator)formula.op () ).target ( formula );
        }
        if(formula.op() != Op.DIA)
            throw new IllegalStateException(
                "Diamondoperator expected at top of "+ formula+" in "+s);
        return formula.javaBlock().program();
    }



    static int varNr = 0;

    private Term sequentState(Sequent s) {
        Term progTerm = s.succedent().getFirst().formula();
        Term result = null;

        Term gamma = TermFactory.DEFAULT.createJunctorTerm(Op.TRUE);
        for(IteratorOfConstrainedFormula icf = s.antecedent().iterator();
            icf.hasNext();) {
            gamma = TermFactory.DEFAULT.createJunctorTerm(Op.AND, gamma,
                                        icf.next().formula());
        }
        
        if (progTerm.op() instanceof IUpdateOperator) {
            // TODO: what to change for quantified updates here??? /PR
            
            IUpdateOperator upOp = (IUpdateOperator) progTerm.op();
        
            int nrUps = upOp.locationCount(); // number of updates

	    Term[] locs   = new Term[nrUps];	     
	    Term[] values = new Term[nrUps];
	    Term target = gamma;
	    for (int k = 0; k<nrUps; k=k+1) { //fix update with new vars
	        locs[k] = upOp.location(progTerm, k);
                LogicVariable newVar = new LogicVariable(
                    new Name("neww"+varNr++), upOp.value(progTerm,k).sort());
                values[k] = TermFactory.DEFAULT.createVariableTerm(newVar);
	    }	  
            result = TermFactory.DEFAULT.createUpdateTerm(locs, values, target); // apply update to gamma
            
            for(int k=0; k<nrUps; k++) { // add equations for "new" values
                // XXX: here more work has to be done if x is more complex
                Term left = locs[k];
                target = upOp.value(progTerm,k);
                Term right = TermFactory.DEFAULT.
                    createUpdateTerm(locs, values, target);
                Term updEqTerm = TermFactory.DEFAULT.createEqualityTerm(
                   left, right);
                result = TermFactory.DEFAULT.createJunctorTerm(Op.AND, 
                    result, updEqTerm);
            }
            
                
            for(int k=0; k<nrUps; k++) { // quantify existentially
                result = TermFactory.DEFAULT.createQuantifierTerm(
                    Op.EX, (LogicVariable)values[k].op(), result);
            }
                
        } else result = gamma;
        
        return result;
    }


    int nr=0;

    public boolean syntacticNonInterference(Node a, Node b){

System.err.println(nr++);
	//get TacletApp for Instantiations
	TacletApp tapp1 = (TacletApp) a.getAppliedRuleApp();
	TacletApp tapp2 = (TacletApp) b.getAppliedRuleApp();
        if ("empty_modality".equals(tapp1.rule().name().toString())) 
            return false;

	//get Read-Sets 
	ListOfSchemaVariable readVars1 = tapp1.taclet().readSet(); 
	ListOfSchemaVariable readVars2 = tapp2.taclet().readSet();
	ListOfSchemaVariable writeVars1 = tapp1.taclet().writeSet(); 
	ListOfSchemaVariable writeVars2 = tapp2.taclet().writeSet();

        if (hasIntersection(instantiate(readVars1, tapp1), 
                            instantiate(writeVars2, tapp2)))
            return false;
        if (hasIntersection(instantiate(readVars2, tapp2), 
                            instantiate(writeVars1, tapp1)))
            return false;
        if (hasIntersection(instantiate(writeVars1, tapp1), 
                            instantiate(writeVars2, tapp2)))
            return false;
            
        return true;
    }


    
    private Vector instantiate(ListOfSchemaVariable vlist, TacletApp tapp) {
//System.err.print(vlist+"->");
        Vector result = new Vector(5);
	IteratorOfSchemaVariable vit =  vlist.iterator(); 
	while (vit.hasNext()) {
            Object inst = tapp.instantiations().getInstantiation(vit.next()); 
	    if (inst instanceof Literal) continue;
            if (inst instanceof ProgramVariable) continue;
            if ((inst instanceof FieldReference) &&
                (((FieldReference)inst).getProgramVariable().isImplicit())) continue;
            result.add(inst);
        }
//System.err.println(result);
        return result;
    
    }

    public void setExceptionHandler(KeYExceptionHandler keh){
    }
    
    
    private boolean hasIntersection(Vector l1, Vector l2) {
        for( Enumeration i=l1.elements(); i.hasMoreElements();) {
            Sort s = getSort(i.nextElement());
            for( Enumeration j=l2.elements(); j.hasMoreElements();) 
                if (checkCompatibility(s, getSort(j.nextElement())))
                    return true;
        }
        return false;
                                    
    }
    
    
    public Sort getSort(Object var){
        if (var == null) return null;
	Sort s = null;
        de.uka.ilkd.key.java.abstraction.KeYJavaType kjt = null;
	if(var instanceof FieldReference)
	    kjt = ((FieldReference) var).getKeYJavaType();
	if(var instanceof ProgramVariable)
	    kjt = ((ProgramVariable) var).getKeYJavaType();
if ((var!=null) && (kjt==null)) System.err.println("NULL KJT OF "+var+" "+var.getClass()+" "+kjt);
        s = kjt.getSort();
if ((var!=null) && (s==null)) System.err.println("NULL SORT OF "+var+" "+var.getClass()+" "+kjt);
	return s;
    }

    public boolean checkCompatibility(Sort s1, Sort s2){
	if(s1 == null || s2 == null) return false;
	return (s1.extendsTrans(s2)||(s2.extendsTrans(s1))); 
    }


    
    private Term syncCondition(JavaProgramElement pa, JavaProgramElement pb) {
        Term exa = syncExpr(pa);
        Term exb = syncExpr(pb);
        if ((exa==null) || (exb==null)) return null;
        Term result = TermFactory.DEFAULT.createJunctorTerm(Op.EQUALS, 
            exa, exb);
        result = TermFactory.DEFAULT.createJunctorTerm(Op.NOT, result);
        return result;
    }
    

    public Term syncExpr(JavaProgramElement pp) {
        Expression syncExpr = null;
        ExecutionContext ec = null;
        SourceElement p = pp;
        while (true) {
            if (p instanceof SynchronizedBlock) {
                syncExpr = ((SynchronizedBlock)p).getExpression();
            } else if (p instanceof MethodFrame) {
                ec = (ExecutionContext) ((MethodFrame)p).getExecutionContext();
            } else if (!(p instanceof ProgramPrefix)) {
                break;
            }
            SourceElement pnext = p.getFirstElement();
            if (p==pnext) {
                break;
            } else {
                p = pnext;
            }
        }
        if (syncExpr == null) {
            return null;
        } else {
            return initConfig.getServices().getTypeConverter().
                convertToLogicElement(syncExpr, ec);
        }
    }
    




    public boolean askUserForEnvironment() {
        return true;
    }


    /** returns the path to the Java model.
     */
    public String getJavaPath() throws ProofInputException {
        return null;
    }
    

    /** set the initial configuration used to read an input. It may become
     * modified during reading depending on the modification strategy used
     * for reading.
     */
    public void setInitConfig(InitConfig i) {
    }

    public void readSpecs() {
    }

    public void readActivatedChoices() throws ProofInputException { 
	//nothing to do 
    }

    public SetOfChoice getActivatedChoices() throws ProofInputException {
        return null;
    
    }
    
    /** reads the include section and returns an Includes object.  
     */
    public Includes readIncludes() throws ProofInputException {
        return new Includes();
    }
    
    /** returns the name of the proof obligation input.
     */
    public String name() {
        return "Non-Interference of ... and ...";
    }

    public void startProtocol() {
	// do nothing
    }
    
    
    private class FirstStatementExtractionVisitor extends CreatingASTVisitor {

        private ProgramElement result;
        private Node node;
        
        public FirstStatementExtractionVisitor(ProgramElement root,
                                               Node n,
                                               Services services) {
	    super(root, true, services);
            this.node = n;
        }

        /** starts the walker*/
        public void start() {	
	    stack.push(new ExtList());		
	    walk(root());
	    ExtList el=stack.peek();
	    int i=0;
	    while (!(el.get(i) instanceof ProgramElement)) {
	        i++;
	    }
	    result=(ProgramElement) (stack.peek()).get(i);
        }

        public ProgramElement result() { 	
	    return result;
        }

        public void performActionOnStatementBlock(StatementBlock x) {
            StatementBlock newBlock = x;
            ExtList changeList = stack.peek();
            if (changeList.getFirst() == CHANGED) { //process change in children
                changeList.removeFirst();
                newBlock = new StatementBlock(changeList);
            }

            if (newBlock.getStatementCount()>1) {
	        addChild(
                    new StatementBlock((Statement)newBlock.getFirstElement()));
	        changed();
            } else {
                doDefaultAction(newBlock);
                changed(); // in case of immediately nested blocks
            }
        }


        public void performActionOnIntLiteral(IntLiteral x) {
            ProgramVariable pv = new LocationVariable(
                new ProgramElementName("some_int"),
                x.getKeYJavaType(initConfig.getServices()));
//            node.setGlobalProgVars(getGlobalProgVars().add(pv));
	    addChild(pv);
            changed();
        }


    }
    
    private class ConditionContainer {
        private ConstrainedFormula f;
        private String label;
        
        public ConditionContainer(ConstrainedFormula f, String s) {
            this.f = f;
            this.label = s;
        }
        
        public ConstrainedFormula getFormula() {
            return f;
        }
        
        public String getLabel() {
            return label;
        }
    }
    

}
