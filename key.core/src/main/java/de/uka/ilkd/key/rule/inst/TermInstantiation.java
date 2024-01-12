/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/**
 * This class is used to store the instantiation of a schemavarible if it is a term.
 */
public class TermInstantiation extends InstantiationEntry<Term> {

    private static final RigidnessException RIGIDNESS_EXCEPTION = new RigidnessException(
        "Tried to instantiate a rigid schema variable" + " with a non-rigid term/formula");


    /**
     * creates a new ContextInstantiationEntry
     *
     * @param sv the SchemaVariable that is instantiated
     * @param term the Term the SchemaVariable is instantiated with
     */
    TermInstantiation(SchemaVariable sv, Term term) {
        super(term);
        // TODO: Remove the check below and move it to the matching logic
        // Done for VM based matching
        if (!term.isRigid() && sv.isRigid()) {
            throw RIGIDNESS_EXCEPTION;
        }
    }
}
