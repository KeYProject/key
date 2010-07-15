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


import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
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
	super(new Name("#ResolveQuery"), 2);
    }


    /**
     * checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the @link Term is valid.
     */
    public boolean validTopLevel(Term term) {
	// a meta operator accepts almost everything
	return  term.arity()==arity();
    }

    private ImmutableArray<Expression> createArgumentPVs(Term t, Services services) {
	final ProgramMethod pm = ((ProgramMethod)t.op());
	boolean staticMethod = pm.isStatic() || pm.isConstructor();
	Expression[] result = new Expression[t.arity()-(staticMethod ? 0 : 1)];
	for (int i=0; i<result.length; i++) {            
	    final IProgramVariable parameter = 
                pm.getVariableSpecification(i).getProgramVariable();
            final KeYJavaType argumentType = pm.getParameterType(i);
            result[i] = createPV(parameter.name().toString(), argumentType, services);
	}
	return new ImmutableArray<Expression>(result);
    }

    private ImmutableArray<QuantifiableVariable> collectFreeVariables(Term t){
	ImmutableSet<QuantifiableVariable> qvs = t.freeVars();
	QuantifiableVariable[] qva = new QuantifiableVariable[qvs.size()];
	Iterator<QuantifiableVariable> it = qvs.iterator();
	for(int i=0; it.hasNext(); i++){
	    qva[i] = it.next();
	}
	return new ImmutableArray<QuantifiableVariable>(qva);
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
	    return tf.createJunctorTerm(Op.TRUE);
	}
	addUpdatesLoc = new Term[t.arity()];
	addUpdatesVal = new Term[t.arity()];
	// the last slot is for the subterm of the update term (to
	// be set on a higher recursion level)
	ImmutableArray<Expression> argPVs = createArgumentPVs(t, services);
	
        final ProgramVariable callerPV = 
	    (pm.isStatic() || pm.isConstructor()) ? null : 
                createPV("queryReceiver", t.sub(0).sort(), services);
	// create updates
	for (int i = 0; i<argPVs.size(); i++) {
	    addUpdatesLoc[i] = tf.createVariableTerm
		((ProgramVariable)argPVs.get(i));
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
                ec = new ExecutionContext(new TypeRef(pm.getContainerType()), 
                        services.getJavaInfo().getDefaultMemoryArea(), null);
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
	    ProgramVariable pv = (ProgramVariable)argPVs.get(i);
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
	    result = tf.createUpdateTerm(addUpdatesLoc, 
                addUpdatesVal, addUpdatesTarget);
	}
	if (addDecls!=null) {
	    result = tf.createDiamondTerm(addDecls, result);
	}
	ImmutableArray<QuantifiableVariable> qvs = collectFreeVariables(t);
	if(qvs.size() > 0){
	    result = tf.createQuantifierTerm(Op.ALL, qvs, result);
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
        for (String aCommonQueryPrefix : commonQueryPrefix) {
            if (resultVarName.startsWith(aCommonQueryPrefix)) {
                if (resultVarName.length() > aCommonQueryPrefix.length()) {
                    resultVarName = resultVarName.
                            substring(aCommonQueryPrefix.length()).toLowerCase();
                }
                break;
            }
        }
        return resultVarName;
    }

    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, 
			  Services services) {
	return createProgramMethodSubstitute(term.sub(0), term.sub(1), services);	
    }

    public Sort sort(Term[] term) {
	return Sort.FORMULA;
    }
}
