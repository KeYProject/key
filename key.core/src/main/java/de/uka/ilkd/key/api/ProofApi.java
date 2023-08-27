/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import java.io.IOException;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableList;

/**
 * @author Alexander Weigl
 * @version 1 (21.04.17)
 */
public class ProofApi {
    private final KeYEnvironment<?> env;
    private final Proof proof;

    public ProofApi(Proof proof, KeYEnvironment<?> currentEnv) {
        this.proof = proof;
        this.env = currentEnv;
    }

    public ScriptApi getScriptApi() {
        return new ScriptApi(this);
    }

    /**
     * Save current Proof-> ProofApi
     */
    public void saveProof() throws IOException {
        // TODO
    }

    public KeYEnvironment<?> getEnv() {
        return env;
    }

    public Proof getProof() {
        return proof;
    }

    public List<ProjectedNode> getOpenGoals() {
        ImmutableList<Goal> goals = proof.openGoals();
        return goals.stream().map(g -> new ProjectedNode(g.node(), null))
                .collect(Collectors.toList());
    }

    public ProjectedNode getFirstOpenGoal() {
        return getOpenGoals().get(0);
    }

    public Set<String> getRules() {
        Set<String> s = new TreeSet<>();
        Goal goal = proof.getSubtreeGoals(proof.root()).head();

        for (final BuiltInRule br : goal.ruleAppIndex().builtInRuleAppIndex().builtInRuleIndex()
                .rules()) {
            s.add(br.displayName());
        }

        Set<NoPosTacletApp> set = goal.ruleAppIndex().tacletIndex().allNoPosTacletApps();
        OneStepSimplifier simplifier = MiscTools.findOneStepSimplifier(goal.proof());
        if (simplifier != null && !simplifier.isShutdown()) {
            set.addAll(simplifier.getCapturedTaclets());
        }

        for (final NoPosTacletApp app : set) {
            RuleJustification just = goal.proof().mgt().getJustification(app);
            if (just == null) {
                continue; // do not break system because of this
            }
            s.add(app.taclet().displayName());
        }

        return s;
    }
}
