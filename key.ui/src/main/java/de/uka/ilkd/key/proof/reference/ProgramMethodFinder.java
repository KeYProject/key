/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.ProgramMethod;

public class ProgramMethodFinder implements Visitor {

    private boolean foundProgramMethod = false;

    @Override
    public boolean visitSubtree(Term visited) {
        return false;
    }

    @Override
    public void visit(Term visited) {
        if (visited.op() instanceof ProgramMethod) {
            foundProgramMethod = true;
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
