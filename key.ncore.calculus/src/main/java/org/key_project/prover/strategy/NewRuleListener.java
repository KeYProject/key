/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

/// Interface for tracking new RuleApps
public interface NewRuleListener {

    /// Called when a new RuleApp is added
    void ruleAdded(RuleApp rule, PosInOccurrence pos);

    /// Called when a collection of new RuleApps is added
    void rulesAdded(ImmutableList<? extends RuleApp> rule, PosInOccurrence pos);

}
