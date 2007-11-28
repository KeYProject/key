// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedList;
import java.util.ListIterator;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.annotation.Annotation;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.ExtList;


/**
 * Walks through a java AST in depth-left-fist-order. 
 * This walker is used to transform a loop (not only 
 * while loops) according to the rules of the dynamic logic.
 */
public class WhileInvariantTransformation extends WhileLoopTransformation {

    private Services services = null;
    private JavaInfo javaInfo = null;    

    private ProgramVariable cont = null;
    private ProgramVariable exc = null;
    private ProgramVariable rtrn = null;
    private ProgramVariable brk = null;
    private ProgramVariable thrownExc = null;
    private ProgramVariable excParam = null;
    private ProgramVariable returnExpr = null;
    
    private boolean continueOccurred = false;
    private boolean returnOccurred = false;

    private LinkedList breakList = null;
    
    /** 
     * creates the WhileLoopTransformation for the transformation mode
     * @param root the ProgramElement where to begin
     * @param outerLabel the ProgramElementName of the outer label 
     * @param innerLabel the ProgramElementName of the inner label 
     */
    public WhileInvariantTransformation(ProgramElement root, 
					ProgramElementName outerLabel,
					ProgramElementName innerLabel,
					ProgramVariable cont,
					ProgramVariable exc,
					ProgramVariable excParam,
					ProgramVariable thrownException,
					ProgramVariable brk,
					ProgramVariable rtrn,
					ProgramVariable returnExpr,
					LinkedList breakList,
					Services services) {

	super(root, outerLabel, innerLabel);
	this.services = services;
	this.cont = cont;
	this.exc = exc;
	this.excParam = excParam;
	this.thrownExc = thrownException;
	this.rtrn = rtrn;
	this.brk = brk;
	this.returnExpr = returnExpr;
	this.breakList = breakList;
	this.javaInfo = this.services.getJavaInfo();
    }


    /** creates the  WhileLoopTransformation for the check mode
     * @param root the ProgramElement where to begin
     * @param inst the SVInstantiations if available
     */
    public WhileInvariantTransformation(ProgramElement root, 
					SVInstantiations inst) {
	super(root, inst);
	this.breakList = new LinkedList();
    }


    /** returns true iff the loop to be transformed
     * contains a continue referring to this loop
     */
    public boolean continueOccurred(){
	return continueOccurred;
    }

    /** return true iff the loop to be transformed
     * contains a return statement leading to abrupt
     * termination of the loop body
     */
    public boolean returnOccurred(){
	return returnOccurred;
    }

    /** returns a list of breaks that lead to
     * abrupt termination of the loop and 
     * have to be replaced
     */
    public LinkedList breakList() {
	return breakList;
    }

    public void performActionOnReturn(Return x) {
	boolean matched = true;
	if (!methodStack.empty()) 
	    methodStack.pop();
        else 
	    matched = false;
	    
	if (!matched) {
	    if (runMode == CHECK) {
		needInnerLabel = true;
	    } else {
		ExtList changeList = (ExtList)stack.peek();
		if (!changeList.isEmpty() &&
		    changeList.getFirst() == CHANGED) {
		    changeList.removeFirst();
		}	
		returnOccurred = true;
		Statement assignFlag = 
		    KeYJavaASTFactory.assign(rtrn, BooleanLiteral.TRUE);
		final Statement[] stmnts;
		if (returnExpr != null) {
		    Statement assignExpr = 
			KeYJavaASTFactory.assign(returnExpr, 
						 x.getExpression());
		    stmnts = new Statement[]{assignFlag,  
					     assignExpr,
					     breakInnerLabel};
		} else
		    stmnts = new Statement[]{assignFlag,  
					     breakInnerLabel};
		addChild(new StatementBlock(stmnts));
		changed();
	    }
	} else
	    doDefaultAction(x);
    }

    protected void performActionOnAnnotationArray(Annotation[] a){
	//do nothing;
    }

    public void performActionOnContinue(Continue x)   {
	if (replaceJumpStatement(x) ||
	    ((x.getLabel() != null) &&
	     (labelStack.search(x.getLabel())==-1))) {
	    continueOccurred = true;
	    if (runMode == CHECK) {
		needInnerLabel = true;
	    } else {
		Statement assign = 
		    KeYJavaASTFactory.assign(cont, BooleanLiteral.TRUE);
		Statement[] stmnts = {assign, breakInnerLabel};
		addChild(new StatementBlock(stmnts));
		changed();
	    }
	} else {
	    doDefaultAction(x);
	}
    }

    public void performActionOnBreak(Break x) {
	boolean replaced = false;
	if (replaceJumpStatement(x) ||
	    ((x.getLabel() != null) &&
	     (labelStack.search(x.getLabel())==-1))) {
	    if (runMode == CHECK) {
		needInnerLabel = true;
		breakList.add(new BreakToBeReplaced(x));
	    } else {
		ListIterator it = breakList.listIterator(0);
		while (it.hasNext()) {
		    BreakToBeReplaced b = (BreakToBeReplaced)it.next();
		    if (x == b.getBreak()) {
			Statement assignFlag = 
			    KeYJavaASTFactory.assign(brk, BooleanLiteral.TRUE);
			Statement assign = 
			    KeYJavaASTFactory.assign
			    (b.getProgramVariable(), BooleanLiteral.TRUE);			
			Statement[] stmnts = {assignFlag, 
					      assign, 
					      breakInnerLabel};
			replaced = true;
			addChild(new StatementBlock(stmnts));
			changed();
			break;
		    }			
		}
		if (!replaced)
		    doDefaultAction(x);
	    }
	} else {
	    doDefaultAction(x);
	}
    }

    
     public void performActionOnWhile(While x)     {
 	ExtList changeList = (ExtList)stack.peek();
 	if (replaceBreakWithNoLabel == 0) {
	    // the most outer while loop
 	    // get guard
 	    if (changeList.getFirst() == CHANGED) {
 		changeList.removeFirst();
 	    }
 	    Expression guard = 
		((Guard) changeList.removeFirst()).getExpression();
 	    Statement body = (Statement) (changeList.isEmpty() ?
 					  null :
 					  changeList.removeFirst());
	    body = KeYJavaASTFactory.ifThen(x.getGuardExpression(), body);
  	    if (breakInnerLabel != null) {
		// an unlabeled continue needs to be handled with (replaced)
  		body = new LabeledStatement(breakInnerLabel.getLabel(),
  					    body);
  	    }
  	    StatementBlock block = new StatementBlock(body);
 	    Statement newBody = block;
  	    if (breakOuterLabel != null) {
  		// an unlabeled break occurs in the
  		// while loop therefore we need a labeled statement
  		newBody =  new LabeledStatement(breakOuterLabel.getLabel(),
 						block);
		
  	    } 

	    Statement[] catchStatements = 
		{KeYJavaASTFactory.assign(exc ,BooleanLiteral.TRUE),
		 KeYJavaASTFactory.assign(thrownExc, excParam)};

	    Catch ctch = KeYJavaASTFactory.catchClause
		(KeYJavaASTFactory.parameterDeclaration(javaInfo,
							javaInfo.getKeYJavaType
							("java.lang.Throwable"),
							excParam), 
		 new StatementBlock(catchStatements));
	    
	    Branch[] branch = {ctch};
	    Statement res = new Try(new StatementBlock(newBody), branch);
 	    addChild(res);
 	    changed();
 	} else {
 	    if (!changeList.isEmpty() &&
		changeList.getFirst() == CHANGED) {
 		changeList.removeFirst();
		Expression guard = 
		    ((Guard) changeList.removeFirst()).getExpression();
 		Statement body = (Statement) (changeList.isEmpty() ?
 					      null :
 					      changeList.removeFirst());
 		addChild(new While(guard, body, x.getPositionInfo(), 
				   x.getAnnotations()));
 		changed();
 	    } else {
 		doDefaultAction(x);
 	    }
 	}
     }
    


}
