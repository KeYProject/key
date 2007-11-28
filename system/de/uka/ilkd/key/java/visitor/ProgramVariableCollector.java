// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.visitor;

import java.util.HashSet;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.annotation.Annotation;
import de.uka.ilkd.key.java.annotation.LoopInvariantAnnotation;
import de.uka.ilkd.key.logic.ArrayOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AttributeOp;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/** 
 * Walks through a java AST in depth-left-fist-order. 
 * This walker is used collect all ProgramVariables in a program.
 */
public class ProgramVariableCollector extends JavaASTVisitor {

    private HashSet result = new HashSet();
    private boolean wAnnotations;

    /**
     * collects all program variables occuring in the AST <tt>root</tt>
     * using this constructor is equivalent to <tt>ProggramVariableCollector(root, false)</tt> 
     * @param root the ProgramElement which is the root of the AST
     */
    public ProgramVariableCollector(ProgramElement root) {
	super(root);
    }

    /**
     * collects all program variables occuring in the AST <tt>root</tt>
     * 
     * @param root the ProgramElement which is the root of the AST
     * @param wAnnotations a boolean flag, if set to true program variables in
     * annotations will be collected, too
     */
    public ProgramVariableCollector(ProgramElement root, boolean wAnnotations) {
        super(root);
        this.wAnnotations = wAnnotations;
    }

    
    /** the action that is performed just before leaving the node the
     * last time 
     */
    protected void doAction(ProgramElement node) {
	node.visit(this);
    }
    
    /** starts the walker*/
    public void start() {	
	walk(root());	
    }

    public HashSet result() { 
	return result;
    }    

    public String toString() {
	return result.toString();
    }

    protected void doDefaultAction(SourceElement x) {
    }

    public void performActionOnProgramVariable(ProgramVariable pv) {
	result.add(pv);
    }
    
    private void performActionOnTerm(Term t) {
	if(t != null){
	    if (t.op() instanceof AttributeOp) {
		result.add(((AttributeOp) t.op()).attribute());
	    } else if (t.op() instanceof ProgramVariable) {
		result.add(t.op());
	    }
	    
	    for (int i = 0, ar = t.arity(); i<ar; i++) {
		performActionOnTerm(t.sub(i));
	    }
	}
    }
     
    
    
    public void performActionOnAnnotationArray(Annotation[] a){
        if (wAnnotations) {
            for(int i = 0; i<a.length; i++){
                if (a[i] instanceof LoopInvariantAnnotation) {
                    LoopInvariantAnnotation lia = (LoopInvariantAnnotation)a[i];
		    if (lia.invariant() != null) {
			performActionOnTerm(lia.invariant());
		    } 
		   
		    if (lia.variant() != null) {
			performActionOnTerm(lia.variant());
		    }

		    if (lia.post() != null) {
			performActionOnTerm(lia.post());
		    }

                    if(lia.getWorkingSpace()!=null){
                        performActionOnTerm(lia.getWorkingSpace());
                    }
                    
                    final ArrayOfTerm terms = lia.olds();
                    for (int j = 0, len = terms.size(); j<len; j++) {
                        performActionOnTerm(terms.getTerm(j));
                    }
                } else {
                    doDefaultAction(a[i]);
                }
            } 
        }
    }

    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);        
    }

    public void performActionOnProgramConstant(ProgramConstant x) {       
        performActionOnProgramVariable(x);
    }
  
    
}
