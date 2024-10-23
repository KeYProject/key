/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.logic.Term;
import org.key_project.logic.Visitor;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

public class BoundVarsVisitor implements Visitor<@NonNull Term> {
    private ImmutableSet<QuantifiableVariable> bdVars = DefaultImmutableSet.nil();

    /**
     * creates a Visitor that collects all bound variables for the subterms of the term it is called
     * from.
     */
    public BoundVarsVisitor() {
    }

    /**
     * only called by execPostOrder in Term.
     */
    public void visit(Term visited) {
        for (int i = 0, ar = visited.arity(); i < ar; i++) {
            for (int j = 0,
                    boundVarsSize = visited.varsBoundHere(i).size(); j < boundVarsSize; j++) {
                bdVars = bdVars.add(visited.varsBoundHere(i).get(j));
            }
        }
    }

    /**
     * visits a sequent
     */
    public void visit(Sequent visited) {
        for (var sf : visited) {
            visit(sf.formula());
        }
    }

    /**
     * returns all the bound variables that have been stored
     */
    public ImmutableSet<QuantifiableVariable> getBoundVariables() {
        return bdVars;
    }
}
