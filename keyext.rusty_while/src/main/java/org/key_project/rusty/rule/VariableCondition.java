/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.sv.SchemaVariable;

/**
 * The instantiations of a schemavariable can be restricted on rule scope by attaching conditions on
 * these variables. Such a condition is realized by a class which implements this interface.
 *<br>
 * The usual place where to put these implementations is inside package
 * <code>de.uka.ilkd.key.rule.conditions</code>. For variable conditions that know only black and
 * white answers there exists a convenience class
 * .
 */
public interface VariableCondition {
    /**
     * checks if the condition for a correct instantiation is fulfilled
     *
     * @param var the SchemaVariable to be instantiated
     * @param instCandidate the SVSubstitute (e.g. Term, ProgramElement) to be mapped to var
     * @param matchCond the MatchCondition with the current matching state and in particular the
     *        SVInstantiations that are already known to be needed
     * @param services the program information object
     * @return modified match results if the condition can be satisfied, or <code>null</code>
     *         otherwise
     */
    MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
                          MatchConditions matchCond,
                          Services services);
}
