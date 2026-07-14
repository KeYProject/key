/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ProgramMethod;

import org.key_project.logic.Visitor;

/**
 * Simple visitor to find instances of non-model {@link ProgramMethod} in terms.
 *
 * @author Arne Keller
 */
public class ProgramMethodFinder implements Visitor<JTerm> {

    /**
     * Whether a program method has been found.
     */
    private boolean foundProgramMethod = false;

    @Override
    public boolean visitSubtree(JTerm visited) {
        // visit all sub-terms
        return true;
    }

    @Override
    public void visit(JTerm visited) {
        if (visited.op() instanceof ProgramMethod pm) {
            if (!pm.isModel()) {
                foundProgramMethod = true;
            }
        }
    }

    @Override
    public void subtreeEntered(JTerm subtreeRoot) {

    }

    @Override
    public void subtreeLeft(JTerm subtreeRoot) {

    }

    public boolean getFoundProgramMethod() {
        return foundProgramMethod;
    }
}
