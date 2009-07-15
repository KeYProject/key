// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class ResolveQuery extends AbstractMetaOperator {

    private Term[] addUpdatesLoc = null;
    private Term[] addUpdatesVal = null;
    private Term addUpdatesTarget;
    private JavaBlock addJavaBlock = null;
    private JavaBlock addDecls = null;
    private TermFactory tf = TermFactory.DEFAULT;
//    private boolean stop = false;    

    
    public ResolveQuery() {
	super(new Name("#ResolveQuery"), 2, Sort.FORMULA);
    }


    private ArrayOfExpression createArgumentPVs(Term t, Services services) {
	final ProgramMethod pm = ((ProgramMethod)t.op());
	boolean staticMethod = pm.isStatic() || pm.isConstructor();
	Expression[] result = new Expression[t.arity()-(staticMethod ? 0 : 1)];
	for (int i=0; i<result.length; i++) {            
	    final IProgramVariable parameter = 
                pm.getVariableSpecification(i).getProgramVariable();
            final KeYJavaType argumentType = pm.getParameterType(i);
            result[i] = createPV(parameter.name().toString(), argumentType, services);
	}
	return new ArrayOfExpression(result);
    }

    private ArrayOfQuantifiableVariable collectFreeVariables(Term t){
	SetOfQuantifiableVariable qvs = t.freeVars();
	QuantifiableVariable[] qva = new QuantifiableVariable[qvs.size()];
	IteratorOfQuantifiableVariable it = qvs.iterator();
	for(int i=0; it.hasNext(); i++){
	    qva[i] = it.next();
	}
	return new ArrayOfQuantifiableVariable(qva);
    }

    private ProgramVariable createPV(String name, Sort s, Services services) {       
        return createPV(name, services.getJavaInfo().getKeYJavaType(s), services);
    }

    private ProgramVariable createPV(String name, KeYJavaType kjt, Services services) {
       
        final ProgramElementName pvname 
            = services.getVariableNamer().getTemporaryNameProposal(name);
        
        return new LocationVariable(pvname, kjt);
    }
    
    private Term createProgramMethodSubstitute(Term t, Term rigidResTerm, Services services) {
	ProgramMethod pm = (ProgramMethod) t.op();
	if(t.arity() > 0 && !pm.isStatic() && !pm.isConstructor() && 
	   t.sub(0).sort() instanceof NullSort){
	    return tf.createJunctorTerm(Junctor.TRUE);
	}
	addUpdatesLoc = new Term[t.arity()];
	addUpdatesVal = new Term[t.arity()];
	// the last slot is for the subterm of the update term (to
	// be set on a higher recursion level)
	ArrayOfExpression argPVs = createArgumentPVs(t, services);
	
        final ProgramVariable callerPV = 
	    (pm.isStatic() || pm.isConstructor()) ? null : 
                createPV("queryReceiver", t.sub(0).sort(), services);
	// create updates
	for (int i = 0; i<argPVs.size(); i++) {
	    addUpdatesLoc[i] = tf.createVariableTerm
		((ProgramVariable)argPVs.getExpression(i));
	    addUpdatesVal[i] = 
		t.sub(i + (pm.isStatic() || pm.isConstructor() ? 0 : 1));
	}
	if (!pm.isStatic() || pm.isConstructor()) {
	    addUpdatesLoc[addUpdatesLoc.length-1] = tf.createVariableTerm(callerPV);
	    addUpdatesVal[addUpdatesVal.length-1] = t.sub(0);
	}	
	// create java block
        final ProgramVariable res = createPV(suggestResultVariableName(pm), t.sort(), services);
	Statement mbs = null;
	//    = new MethodBodyStatement(pm, callerPV, res, argPVs); 
        //    (for always binding dynamically)
	if (pm.isConstructor() || pm.isStatic() || pm.isPrivate()) { //static binding
	    mbs = new MethodBodyStatement(pm, callerPV, res, argPVs);
	} else { //dynamic binding
	    mbs = new MethodReference(argPVs, pm.getProgramElementName(),
	                                    callerPV);
            mbs = new CopyAssignment(res, (Expression) mbs);
            
            final ExecutionContext ec; 
            if (pm.getContainerType() != null) {
                ec = new ExecutionContext(new TypeRef(pm.getContainerType()), null);
            } else {
                ec = services.getJavaInfo().getDefaultExecutionContext();
            }
            mbs = new MethodFrame(null, ec, new StatementBlock(mbs));
            
        }            
        
	addJavaBlock = JavaBlock.createJavaBlock(new StatementBlock(mbs));
	// create local var declaration java block
	LocalVariableDeclaration[] vardecls 
	    = new LocalVariableDeclaration[t.arity()+1]; 
	vardecls[0] = new LocalVariableDeclaration
	    (new TypeRef(res.getKeYJavaType()), 
	     new VariableSpecification(res)); 
	for (int i=0; i<argPVs.size(); i++) {
	    ProgramVariable pv = (ProgramVariable)argPVs.getExpression(i);
	    vardecls[i+1] = new LocalVariableDeclaration
		(new TypeRef(pv.getKeYJavaType()), 
		 new VariableSpecification(pv));
	}
	if (!(pm.isStatic() || pm.isConstructor())) {
	    vardecls[vardecls.length-1] = new LocalVariableDeclaration
		(new TypeRef(callerPV.getKeYJavaType()), 
		 new VariableSpecification(callerPV));
	}
	addDecls = JavaBlock.createJavaBlock(new StatementBlock(vardecls));
	Term resTerm = tf.createVariableTerm(res);
	Term eq1 = tf.createEqualityTerm(resTerm, rigidResTerm);
	Term result = tf.createBoxTerm(addJavaBlock, eq1);
	if (addUpdatesLoc!=null && addUpdatesLoc.length>0) {
	    addUpdatesTarget = result;
	    result = TB.applyParallel(services, addUpdatesLoc, 
                addUpdatesVal, addUpdatesTarget);
	}
	if (addDecls!=null) {
	    result = tf.createDiamondTerm(addDecls, result);
	}
	ArrayOfQuantifiableVariable qvs = collectFreeVariables(t);
	if(qvs.size() > 0){
	    result = tf.createQuantifierTerm(Quantifier.ALL, qvs, result);
	}
	return result;
    }


    /**
     * generates a proposal for naming the result variable depending on the
     * methods name
     * @param pm the ProgramMethod     
     */
    private String suggestResultVariableName(ProgramMethod pm) {
        String resultVarName = pm.getName();
        
        final String[] commonQueryPrefix = new String[]{"is", "has", "get"};
        for (int i = 0; i<commonQueryPrefix.length; i++) {
            if (resultVarName.startsWith(commonQueryPrefix[i])) {
                if (resultVarName.length() > commonQueryPrefix[i].length()) {
                    resultVarName = resultVarName.
                        substring(commonQueryPrefix[i].length()).toLowerCase();                    
                }
                break;
            }
        }
        return resultVarName;
    }


    public Term calculate(Term term, SVInstantiations svInst, 
			  Services services) {
	return createProgramMethodSubstitute(term.sub(0), term.sub(1), services);	
    }
}
