// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedList;
import java.util.ListIterator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Continue;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 * Walks through a java AST in depth-left-fist-order. This walker is used to
 * transform a loop (not only while loops) according to the rules of the dynamic
 * logic.
 */
public class WhileInvariantTransformation extends WhileLoopTransformation {

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

    private LinkedList<BreakToBeReplaced> breakList = null;

    /**
     * creates the WhileLoopTransformation for the transformation mode
     * 
     * @param root
     *            the ProgramElement where to begin
     * @param outerLabel
     *            the ProgramElementName of the outer label
     * @param innerLabel
     *            the ProgramElementName of the inner label
     */
    public WhileInvariantTransformation(ProgramElement root,
            ProgramElementName outerLabel, ProgramElementName innerLabel,
            ProgramVariable cont, ProgramVariable exc,
            ProgramVariable excParam, ProgramVariable thrownException,
            ProgramVariable brk, ProgramVariable rtrn,
            ProgramVariable returnExpr, 
            LinkedList<BreakToBeReplaced> breakList, Services services) {

	super(root, outerLabel, innerLabel, services);
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

    /**
     * creates the WhileLoopTransformation for the check mode
     * 
     * @param root
     *            the ProgramElement where to begin
     * @param inst
     *            the SVInstantiations if available
     */
    public WhileInvariantTransformation(ProgramElement root,
					SVInstantiations inst,
                                        Services services) {
	super(root, inst, services);
        this.breakList = new LinkedList<BreakToBeReplaced>();
    }

    /**
     * returns true iff the loop to be transformed contains a continue referring
     * to this loop
     */
    public boolean continueOccurred() {
        return continueOccurred;
    }

    /**
     * return true iff the loop to be transformed contains a return statement
     * leading to abrupt termination of the loop body
     */
    public boolean returnOccurred() {
        return returnOccurred;
    }

    /**
     * returns a list of breaks that lead to abrupt termination of the loop and
     * have to be replaced
     */
    public LinkedList<BreakToBeReplaced> breakList() {
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
                ExtList changeList =  stack.peek();
                if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
                    changeList.removeFirst();
                }
                returnOccurred = true;
                Statement assignFlag =
                        KeYJavaASTFactory.assign(rtrn, BooleanLiteral.TRUE);
		final StatementBlock stmnts;
                if (returnExpr != null) {
		    // Keep the PositionInfo because it is required for symbolic
		    // execution tree extraction and this assignment is the only
		    // unique representation of the replaced return
		    Statement assignExpr = KeYJavaASTFactory.assign(returnExpr,
			    x.getExpression(), x.getPositionInfo());
		    stmnts = KeYJavaASTFactory.block(assignFlag, assignExpr,
			    breakInnerLabel);
                } else
		    // Keep the PositionInfo because it is required for symbolic
		    // execution tree extraction and there is no other unique
		    // representation of the replaced return
		    stmnts = KeYJavaASTFactory.block(
			    assignFlag,
			    KeYJavaASTFactory.breakStatement(
				    breakInnerLabel.getLabel(),
				    x.getPositionInfo()));
		addChild(stmnts);
                changed();
            }
        } else
            doDefaultAction(x);
    }


    public void performActionOnContinue(Continue x) {
        if (replaceJumpStatement(x)
                || ((x.getLabel() != null) && (labelStack.search(x.getLabel()) == -1))) {
            continueOccurred = true;
            if (runMode == CHECK) {
                needInnerLabel = true;
            } else {
                Statement assign =
                        KeYJavaASTFactory.assign(cont, BooleanLiteral.TRUE);
		// Keep the PositionInfo because it is required for symbolic
		// execution tree extraction and there is no other unique
		// representation of the replaced continue
		addChild(KeYJavaASTFactory.block(assign, KeYJavaASTFactory
			.breakStatement(breakInnerLabel.getLabel(),
				x.getPositionInfo())));
                changed();
            }
        } else {
            doDefaultAction(x);
        }
    }

    public void performActionOnBreak(Break x) {
        boolean replaced = false;
        if (replaceJumpStatement(x)
                || ((x.getLabel() != null) && (labelStack.search(x.getLabel()) == -1))) {
            if (runMode == CHECK) {
                needInnerLabel = true;
                breakList.add(new BreakToBeReplaced(x));
            } else {
                ListIterator<BreakToBeReplaced> it = breakList.listIterator(0);
                while (it.hasNext()) {
                    BreakToBeReplaced b = it.next();
                    if (x == b.getBreak()) {
                        Statement assignFlag =
                                KeYJavaASTFactory.assign(brk,
                                        BooleanLiteral.TRUE);
			// Keep the PositionInfo because it is required for
			// symbolic execution tree extraction and this
			// assignment is the only unique representation of the
			// replaced break
			Statement assign = KeYJavaASTFactory.assign(
				b.getProgramVariable(), BooleanLiteral.TRUE,
				x.getPositionInfo());
                        replaced = true;
			addChild(KeYJavaASTFactory.block(assignFlag, assign,
				breakInnerLabel));
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

    public void performActionOnWhile(While x) {
        ExtList changeList = stack.peek();
        if (replaceBreakWithNoLabel == 0) {
            // the most outer while loop
            // get guard
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
            }
            @SuppressWarnings("unused")
            Expression guard =
                    ((Guard) changeList.removeFirst()).getExpression();
            Statement body =
                    (Statement) (changeList.isEmpty() ? null
                            : changeList.removeFirst());
            body = KeYJavaASTFactory.ifThen(x.getGuardExpression(), body);
            if (breakInnerLabel != null) {
                // an unlabeled continue needs to be handled with (replaced)
		body = KeYJavaASTFactory.labeledStatement(
			breakInnerLabel.getLabel(), body);
            }
	    StatementBlock block = KeYJavaASTFactory.block(body);
            Statement newBody = block;
            if (breakOuterLabel != null) {
                // an unlabeled break occurs in the
                // while loop therefore we need a labeled statement
		newBody = KeYJavaASTFactory.labeledStatement(
			breakOuterLabel.getLabel(), block);

            }

            Statement[] catchStatements =
                    { KeYJavaASTFactory.assign(exc, BooleanLiteral.TRUE),
                            KeYJavaASTFactory.assign(thrownExc, excParam) };

	    Catch ctch = KeYJavaASTFactory
		    .catchClause(KeYJavaASTFactory.parameterDeclaration(
			    javaInfo,
			    javaInfo.getKeYJavaType("java.lang.Throwable"),
			    excParam), catchStatements);

            Branch[] branch = { ctch };
	    Statement res = KeYJavaASTFactory.tryBlock(newBody, branch);
            addChild(res);
            changed();
        } else {
            if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
                Expression guard =
                        ((Guard) changeList.removeFirst()).getExpression();
                Statement body =
                        (Statement) (changeList.isEmpty() ? null
                                : changeList.removeFirst());
		addChild(KeYJavaASTFactory.whileLoop(guard, body,
			x.getPositionInfo()));
                changed();
            } else {
                doDefaultAction(x);
            }
        }
    }

    /**
     * Transform the body of an enhanced for loop for usage with
     * invariant-theorems.
     * 
     * The following restriction is made for enhanced for loops:
     * There is only one label (no inner/outer pair) needed, so
     * innerlabel and outerlabel must be the same.
     * 
     * The loop body is transformed like for a while loop 
     * (break/continue/return replaced, try+catch added).
     * 
     * If the top loop is an enhancedFor-loop transform it  
     * like a while loop.
     * 
     * Due to the fact that the condition in enhanced loops has no
     * side effects, things can be put easier here.
     * 
     * If the loop is not top most, act like the super class.
     */
    public void performActionOnEnhancedFor(EnhancedFor x) {
        ExtList changeList =  stack.peek();
        if (replaceBreakWithNoLabel == 0) {
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
            }
            
            if(breakInnerLabel != breakOuterLabel)
                Debug.log4jWarn("inner and outer label must be the same in WhileInvariantTransformation.performActionOnEnhancedFor", null);
            
            Statement body = changeList.get(Statement.class);
            
            // label statement if there are returns / continue / breaks
            if (breakOuterLabel != null) {
		body = KeYJavaASTFactory.labeledStatement(
			breakOuterLabel.getLabel(), body);

            }
            
            Statement[] catchStatements =
                    { KeYJavaASTFactory.assign(exc, BooleanLiteral.TRUE),
                            KeYJavaASTFactory.assign(thrownExc, excParam) };

	    Catch ctch = KeYJavaASTFactory.catchClause(KeYJavaASTFactory
		    .parameterDeclaration(javaInfo,
			    javaInfo.getKeYJavaType("java.lang.Throwable"),
			    excParam), catchStatements);

	    addChild(KeYJavaASTFactory.tryBlock(body, ctch));
            changed();
        } else {
            super.performActionOnEnhancedFor(x);
        }
    }

}
