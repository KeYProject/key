/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;


import org.key_project.prover.sequent.PosInOccurrence;


/**
 * rule application with specific information how and where the rule has to be applied
 */
public interface RuleApp
        extends org.key_project.prover.rules.RuleApp {

    /**
     * returns the rule of this rule application
     */
    org.key_project.prover.rules.Rule rule();

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and a position in the
     * corresponding formula) of this rule application
     */
    PosInOccurrence posInOccurrence();
}
