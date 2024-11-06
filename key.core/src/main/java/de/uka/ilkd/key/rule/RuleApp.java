/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;


import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.util.EqualsModProofIrrelevancy;

import org.jspecify.annotations.NonNull;


/**
 * rule application with specific information how and where the rule has to be applied
 */
public interface RuleApp
        extends org.key_project.ncore.rules.RuleApp, EqualsModProofIrrelevancy {

    /**
     * returns the rule of this rule application
     */
    Rule rule();

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and a position in the
     * corresponding formula) of this rule application
     */
    PosInOccurrence posInOccurrence();

    /**
     * applies the specified rule at the specified position if all schema variables have been
     * instantiated
     *
     * TODO: better name
     *
     * @param goal the Goal where to apply the rule
     */
    void execute(Namespace<? super @NonNull Function> fns);
}
