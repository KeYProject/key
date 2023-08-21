/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.ProgramMethod;

/**
 * Simple visitor to find instances of non-model {@link ProgramMethod} in terms.
 *
 * @author Arne Keller
 */
public class ProgramMethodFinder implements Visitor {

    /**
     * Whether a program method has been found.
     */
    private boolean foundProgramMethod = false;

    @Override
    public boolean visitSubtree(Term visited) {
        return false;
    }

    @Override
    public void visit(Term visited) {
        if (visited.op() instanceof ProgramMethod) {
            ProgramMethod pm = (ProgramMethod) visited.op();
            if (!pm.isModel()) {
                foundProgramMethod = true;
            }
        }
    }

    @Override
    public void subtreeEntered(Term subtreeRoot) {

    }

    @Override
    public void subtreeLeft(Term subtreeRoot) {

    }

    public boolean getFoundProgramMethod() {
        return foundProgramMethod;
    }
}
