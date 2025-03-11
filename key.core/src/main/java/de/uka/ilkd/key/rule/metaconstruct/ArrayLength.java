/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ArrayLength extends ProgramTransformer {

    /**
     * creates a typeof ProgramTransformer
     *
     * @param expr the instance of expression contained by the meta construct
     */
    public ArrayLength(Expression expr) {
        super("#length-reference", expr);

    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations insts) {
        return new ProgramElement[] { KeYJavaASTFactory.fieldReference(services, "length",
            (Expression) pe, insts.getExecutionContext()) };
    }
}
