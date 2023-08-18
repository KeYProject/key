/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.VariableReference;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Creates a true or false literal if the given program element is or is not a static variable
 * reference.
 *
 * @author N/A
 */
public class IsStatic extends ProgramTransformer {

    /**
     * creates a typeof ProgramTransformer
     *
     * @param pe the instance of expression contained by the meta construct
     */
    public IsStatic(ProgramElement pe) {
        super("#isstatic", pe);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        if (pe instanceof VariableReference) {
            if (((VariableReference) pe).getProgramVariable().isStatic()) {
                return new ProgramElement[] { KeYJavaASTFactory.trueLiteral() };
            }
        }
        return new ProgramElement[] { KeYJavaASTFactory.falseLiteral() };
    }
}
