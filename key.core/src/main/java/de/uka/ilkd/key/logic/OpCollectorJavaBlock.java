/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 * Extended {@link OpCollector} that also descends into Java blocks
 * and collects all {@link LocationVariable} there.
 *
 * @author Arne Keller
 */
public class OpCollectorJavaBlock extends OpCollector {
    @Override
    public void visit(Term t) {
        super.visit(t);
        if (t.javaBlock() != JavaBlock.EMPTY_JAVABLOCK) {
            var collect = new JavaASTCollector(t.javaBlock().program(), LocationVariable.class);
            collect.start();
            for (ProgramElement programElement : collect.getNodes()) {
                if (programElement instanceof LocationVariable locationVariable) {
                    ops.add(locationVariable);
                }
            }
        }
    }
}
