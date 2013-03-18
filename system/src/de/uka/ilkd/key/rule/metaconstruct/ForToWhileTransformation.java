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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.ExpressionStatement;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.ExtList;

/**
 * This transformation is used to transform a for-loop into a while-loop.
 * 
 * This is done because there are some rules (invariant, induction, ...) that
 * are only available for while-loops, not for for-loops.
 * 
 * The transformation behaviour is very similar to the superclass' behaviour
 * only the outermost for loop is treated silghtly differently.
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
        ExtList changeList = (ExtList) stack.peek();

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
                    guard  = new Guard(BooleanLiteral.TRUE); 
                }
            } else {
                guard = new Guard(BooleanLiteral.TRUE);
            }

            if (changeList.get(0) instanceof IForUpdates) {
                updates = (IForUpdates) changeList.removeFirst();
            }

            body = (Statement) changeList.removeFirst();

            if (innerLabelNeeded() && breakInnerLabel != null) {
                body = new LabeledStatement(breakInnerLabel.getLabel(), body);
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
            
            outerBlockStatements[initSize] = new While(guard.getExpression(),
                    new StatementBlock(new ImmutableArray<Statement>(
                            innerBlockStatements)), null);

            Statement outerBlock = new StatementBlock(new ImmutableArray<Statement>(
                    outerBlockStatements));

            if (outerLabelNeeded() && breakOuterLabel != null) {
                outerBlock = new LabeledStatement(breakOuterLabel.getLabel(),
                        outerBlock);
            }
            
            // copy loop invariant to the created while loop
            LoopInvariant li 
                = services.getSpecificationRepository().getLoopInvariant(x);
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
