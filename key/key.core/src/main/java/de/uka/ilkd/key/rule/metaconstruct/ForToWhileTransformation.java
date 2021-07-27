// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.expression.ExpressionStatement;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.IForUpdates;
import de.uka.ilkd.key.java.statement.ILoopInit;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.speclang.LoopSpecification;

/**
 * This transformation is used to transform a for-loop into a while-loop.
 * 
 * This is done because there are some rules (invariant, induction, ...) that
 * are only available for while-loops, not for for-loops.
 * 
 * The transformation behaviour is very similar to the superclass' behaviour
 * only the outermost for loop is treated slightly differently.
 * 
 * @see ForToWhile Here is an example
 * @author MU
 * 
 */

public class ForToWhileTransformation extends WhileLoopTransformation {
    
    public ForToWhileTransformation(ProgramElement root,
            ProgramElementName outerLabel, ProgramElementName innerLabel, 
            Services services) {
        super(root, outerLabel, innerLabel, services);
    }

    /**
     * change the for-loop to a while loop with inits and updates.
     */
    public void performActionOnFor(For x) {
        ExtList changeList = stack.peek();

        if (replaceBreakWithNoLabel == 0) {
            // most outer for loop

            if (changeList.getFirst() == CHANGED)
                changeList.removeFirst();

            ILoopInit inits = null;
            IForUpdates updates = null;
            Statement body = null;

            if (changeList.get(0) instanceof ILoopInit) {
                inits = (ILoopInit) changeList.removeFirst();
            }

            Guard guard;            
            if (x.getGuard() != null) {            
                guard = (Guard) changeList.removeFirst();
                if (guard.getExpression() == null) {
		    guard = KeYJavaASTFactory.trueGuard();
                }
            } else {
		guard = KeYJavaASTFactory.trueGuard();
            }

            if (changeList.get(0) instanceof IForUpdates) {
                updates = (IForUpdates) changeList.removeFirst();
            }

            body = (Statement) changeList.removeFirst();

            if (innerLabelNeeded() && breakInnerLabel != null) {
		body = KeYJavaASTFactory.labeledStatement(
			breakInnerLabel.getLabel(), body, PositionInfo.UNDEFINED);
            }

            final int updateSize = (updates == null ? 0 : updates.size());
            
            Statement innerBlockStatements[] = new Statement[updateSize + 1];
            innerBlockStatements[0] = body;
            if (updates != null) {
                for (int copyStatements = 0; copyStatements < updateSize; copyStatements++) {
                    innerBlockStatements[copyStatements + 1] = (ExpressionStatement) updates
                            .getExpressionAt(copyStatements);
                }
            }

            final int initSize = (inits == null ? 0 : inits.size());
            Statement outerBlockStatements[] = new Statement[initSize + 1];

            if (inits != null) {
                for (int copyStatements = 0; copyStatements < initSize; copyStatements++) {
                    outerBlockStatements[copyStatements] = inits.getInits()
                            .get(copyStatements);
                }
            }
            
	    outerBlockStatements[initSize] = KeYJavaASTFactory.whileLoop(
		    guard.getExpression(),
		    KeYJavaASTFactory.block(innerBlockStatements), null);

	    Statement outerBlock = KeYJavaASTFactory
		    .block(outerBlockStatements);

            if (outerLabelNeeded() && breakOuterLabel != null) {
		outerBlock = KeYJavaASTFactory.labeledStatement(
			breakOuterLabel.getLabel(), outerBlock, PositionInfo.UNDEFINED);
            }
            
            // copy loop invariant to the created while loop
            LoopSpecification li 
                = services.getSpecificationRepository().getLoopSpec(x);
            if (li != null) {
                li = li.setLoop((While)outerBlockStatements[initSize]);
                services.getSpecificationRepository().addLoopInvariant(li);
            }

            addChild(outerBlock);
            changed();
        } else {
            super.performActionOnFor(x);
        }
    }

}