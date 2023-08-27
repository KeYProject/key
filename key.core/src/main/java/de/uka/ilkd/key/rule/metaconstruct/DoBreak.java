/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This class performs a labeled break. This means <code>
 *  l1:l2:{l3:{l4:{break l3;}} ...}
 * </code> becomes <code>
 *  l1:l2:{...}
 * </code>
 */
public class DoBreak extends ProgramTransformer {

    /**
     * creates a do-break ProgramTransformer
     *
     * @param labeledBreak the LabeledStatement contained by the meta construct
     */
    public DoBreak(LabeledStatement labeledBreak) {
        super("do-break", labeledBreak);
    }

    /**
     * a helper method to perform the symbolic execution of the doBreak metaconstruct.
     *
     * @param block the NonTerminalProgramElement to go through and look for the label
     * @param breakLabel the Label the break statement marked
     */
    private ProgramElement doBreak(NonTerminalProgramElement block, Label breakLabel, Break b) {

        if (block instanceof LabeledStatement) {
            // we enter a labeled block so we have to check the label
            Label blockLabel = ((LabeledStatement) block).getLabel();
            if (blockLabel.equals(breakLabel)) {
                // skip this block
                return KeYJavaASTFactory.block();
            } else {
                // we assume that the doBreak is only applied in case
                // of success. That is why we create a new
                // LabeledBlock here and why we assume that the body
                // of this LabeledStatement is a NonTerminalProgramElement
                return b;
            }
        }
        return null;
    }

    /**
     * performs the program transformation needed for symbolic program transformation
     *
     * @param services the Services with all necessary information about the java programs
     * @return the transformated program
     */
    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations insts) {
        // get label of break
        // ContextInstantiationEntry ctx = insts.getContextInstantiation();
        // Break breakStmnt = (Break) PosInProgram.
        // getProgramAt(ctx.prefix(), pe);
        LabeledStatement lst = (LabeledStatement) pe;
        Break breakStmnt;
        if (lst.getChildAt(1) instanceof Break) {
            breakStmnt = (Break) lst.getChildAt(1);
        } else {
            breakStmnt = (Break) ((StatementBlock) lst.getChildAt(1)).getChildAt(0);
        }
        return new ProgramElement[] {
            doBreak((NonTerminalProgramElement) pe, breakStmnt.getLabel(), breakStmnt) };
    }
}
