/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.util.collection.ImmutableList;

public interface IBuiltInRuleApp extends RuleApp {

    /**
     * returns the built in rule of this rule application
     */
    BuiltInRule rule();

    /**
     * Tries to complete the rule application from the available information. Attention: Do neither
     * add GUI code to the rules nor use this method directly Instead ask the implementation of the
     * {@link de.uka.ilkd.key.control.UserInterfaceControl} to complete a built-in rule. Returns a
     * complete app only if there is exactly one contract. If you want a complete app for combined
     * contracts, use <code>forceInstantiate</code> instead. For an example implementation see e.g.
     * {@link UseOperationContractRule} or {@link UseDependencyContractRule}.
     */
    IBuiltInRuleApp tryToInstantiate(Goal goal);

    IBuiltInRuleApp forceInstantiate(Goal goal);

    List<LocationVariable> getHeapContext();

    /**
     * returns true if tryToInstantiate may be able to complete the app
     *
     * @return
     */
    boolean isSufficientlyComplete();

    ImmutableList<PosInOccurrence> ifInsts();

    IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts);

    IBuiltInRuleApp replacePos(PosInOccurrence newPos);
}
