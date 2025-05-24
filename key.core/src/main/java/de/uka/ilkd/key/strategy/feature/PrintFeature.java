/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * For debugging purposes. Wraps a feature and prints the computed value
 */
public class PrintFeature implements Feature {
    private static final Logger LOGGER = LoggerFactory.getLogger(PrintFeature.class);

    private final Feature f;
    private final String prefix;

    public PrintFeature(String prefix, Feature f) {
        this.f = f;
        this.prefix = prefix;
    }

    public PrintFeature(Feature f) {
        this("", f);
    }


    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal,
            MutableState mState) {
        RuleAppCost cost = f.computeCost(app, pos, goal, mState);
        LOGGER.debug("{}:{}:{}{}", prefix, cost.toString(), pos != null ? pos.subTerm() + ":" : "",
            app.rule().name());
        return cost;
    }



}
