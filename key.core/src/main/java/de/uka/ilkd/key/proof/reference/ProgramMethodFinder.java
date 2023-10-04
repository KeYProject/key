/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import org.key_project.logic.Visitor;
import de.uka.ilkd.key.logic.op.ProgramMethod;

/**
 * Simple visitor to find instances of non-model {@link ProgramMethod} in terms.
 *
 * @author Arne Keller
 */
public class ProgramMethodFinder implements Visitor<Sort> {

    /**
     * Whether a program method has been found.
     */
    private boolean foundProgramMethod = false;

    @Override
    public boolean visitSubtree(org.key_project.logic.Term<Sort> visited) {
        return false;
    }

    @Override
    public void visit(org.key_project.logic.Term<Sort> visited) {
        if (visited.op() instanceof ProgramMethod pm) {
            if (!pm.isModel()) {
                foundProgramMethod = true;
            }
        }
    }

    @Override
    public void subtreeEntered(org.key_project.logic.Term<Sort> subtreeRoot) {

    }

    @Override
    public void subtreeLeft(org.key_project.logic.Term<Sort> subtreeRoot) {

    }

    public boolean getFoundProgramMethod() {
        return foundProgramMethod;
    }
}
