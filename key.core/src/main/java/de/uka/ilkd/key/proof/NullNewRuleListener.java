/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.NewRuleListener;
import org.key_project.util.collection.ImmutableList;

/**
 * Implementation of the NewRuleListener interface that does nothing
 */
public class NullNewRuleListener implements NewRuleListener {

    @Override
    public void ruleAdded(RuleApp rule, PosInOccurrence pos) {
    }

    @Override
    public void rulesAdded(ImmutableList<? extends RuleApp> rule, PosInOccurrence pos) {
    }

    public static final NewRuleListener INSTANCE = new NullNewRuleListener();

}
