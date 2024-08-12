/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.sv.SchemaVariable;

public interface TacletMatcher {
    /**
     * matches the given term against the taclet's find term if the taclet has no find term or the
     * match is unsuccessful <code>null</code>
     * is returned
     *
     * @param term the Term to be matched against the find expression
     *        of the taclet
     * @param matchCond the MatchConditions with side conditions to be
     *        satisfied, e.g. partial instantiations of schema variables; before
     *        calling this method the constraint contained in the match conditions
     *        must be ensured to be satisfiable, i.e.
     *        {@code matchCond.getConstraint().isSatisfiable()} must return true
     *
     * @param services the Services
     * @return the found schema variable mapping or <code>null</code> if the matching failed
     */
    MatchConditions matchFind(Term term, MatchConditions matchCond,
            Services services);

    /**
     * checks if the conditions for a correct instantiation are satisfied
     *
     * @param var the SchemaVariable to be instantiated
     * @param instantiationCandidate the SVSubstitute, which is a candidate for a possible
     *        instantiation of var
     * @param matchCond the MatchConditions which have to be respected for the new match
     * @param services the Services object encapsulating information about the Java type model
     * @return the match conditions resulting from matching <code>var</code> with
     *         <code>instantiationCandidate</code> or <code>null</code> if a match was not possible
     */
    MatchConditions checkVariableConditions(SchemaVariable var,
            SyntaxElement instantiationCandidate, MatchConditions matchCond, Services services);
}
