// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


/**
 * visitor for <t> execPostOrder </t> of 
 * {@link de.uka.ilkd.key.logic.Term}. Called with that method
 * on a term, the visitor builds a new term replacing all AccessOp-s with
 * ShadowAccessOp-s
 */
package de.uka.ilkd.key.logic;

import java.util.Stack;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.JVMIsTransientMethodBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.util.Debug;


public class ShadowReplaceVisitor extends Visitor{	

    private Term computedResult = null;
    //    private TypeConverter typeConverter = null;

    /**
     * the stack contains the subterms that will be added in the next step of
     * execPostOrder in Term in order to build the new term. A boolean value
     * between or under the subterms on the stack indicate that a term using
     * these subterms should build a new term instead of using the old one,
     * because one of its subterms has been built, too.
     */
    private Stack subStack; //of Term (and Boolean)
    private TermFactory tf = TermFactory.DEFAULT;
    private Boolean newMarker = Boolean.TRUE;


    final Term transactionCounter;

    final static ProgramElementName transactionCounterName = 
	new ProgramElementName(JVMIsTransientMethodBuilder.IMPLICIT_TRANSACTION_COUNTER,
			       "de.uka.ilkd.key.javacard.KeYJCSystem");

    /**
     * @param forceSVInst iff true instantiate uninstantiated SVs by
     * creating new metavariables or new bound logicvariables
     */
    public ShadowReplaceVisitor(Services services) { 
	transactionCounter = 
            tf.createVariableTerm(
                 services.getJavaInfo().getAttribute(transactionCounterName.getProgramName(),
						transactionCounterName.getQualifier()));
	Debug.assertTrue(transactionCounter != null);
	subStack = new Stack(); // of Term
    }

    private Term[] neededSubs(int n) {
	boolean newTerm = false;
	Term[] result = new Term[n];
	for (int i = n-1; i >= 0; i--) {
	    Object top = subStack.pop();
	    if (top == newMarker){
		newTerm = true; 
		top     = subStack.pop();
	    }
	    result[i] = (Term) top;
	}
	if (newTerm && (subStack.empty() || 
			subStack.peek() != newMarker) ) {
	    subStack.push(newMarker);
	}
	return result;
    }

    public void visit(Term visited) {
	Operator op = visited.op();
	boolean changed = false;
	
	if (op instanceof ShadowedOperator){
	    Debug.fail("You should not put #shadowed meta operator around already shadowed object access expressions!");
	}

	if (op instanceof ArrayOp) {       
	    op = ShadowArrayOp.getShadowArrayOp(((ArrayOp)op).arraySort());
	    changed = true;
	} else if (op instanceof AttributeOp) {
	    op = ShadowAttributeOp.getShadowAttributeOp(((AttributeOp)op).attribute());
	    changed = true;
	}

	if (changed && (subStack.empty() || subStack.peek()!=newMarker)) {
	    subStack.push(newMarker);
	}
	
	
	ArrayOfQuantifiableVariable boundVars 
	    = ((visited.varsBoundHere(0).size() == 0) ?
	       visited.varsBoundHere(1) :
	       visited.varsBoundHere(0)); 
	
	
	Term[] neededsubs = neededSubs(visited.arity());

	if (changed || (!subStack.empty() && 
			subStack.peek() == newMarker)) {

	    Operator newOp;
	    if (changed) {
		newOp = op;

		// FIXME - there is a problem with this:
                // Java Card specs say, that after abortTransaction
		// the references to all objects that were initialised during
		// the (aborted) transaction are set to null.
		// This is not solvable (I think) with the current 
		// shadowing mechanism
		if (visited.op() instanceof AttributeOp) {
		    if (((AttributeOp)op).attribute().name().toString().startsWith("<")) {
			// No change, it's a special attribute
			//			System.out.println(neededsubs[1].op().name());
			newOp = visited.op();
		    }
		}
                // prepare extra subterm
		if(newOp != visited.op()) {
		    final Term[] newsubs = new Term[neededsubs.length+1];
		    System.arraycopy(neededsubs, 0, newsubs, 0, neededsubs.length);
		    newsubs[neededsubs.length] = transactionCounter;
		    neededsubs = newsubs;
		}

	    } else {
		newOp = visited.op();
	    }
	    pushNew(tf.createTerm(newOp, 
				  neededsubs,
				  boundVars,
				  visited.javaBlock()));
	} else {
	    subStack.push(visited);
	}		
	
    }

    private void pushNew(Object t) {
	if (subStack.empty() || subStack.peek() != newMarker) {
	    subStack.push(newMarker);
	}
	subStack.push(t);	
    }


    /**
     * delivers the new built term
     */
    public Term getTerm() {
	if (computedResult==null) {
	    Object o=null;
	    do {
		o=subStack.pop();
	    } while (o==newMarker);
	    Term t = (Term) o;
	    computedResult=t;
	}	
	return computedResult;
    }
}
