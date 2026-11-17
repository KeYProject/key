/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.prover.proof.rulefilter.IHTacletFilter;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.strategy.AbstractFeatureStrategy;
import org.key_project.prover.strategy.costbased.feature.ConditionalFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

public abstract class JavaAbstractFeatureStrategy extends AbstractFeatureStrategy<Goal>
        implements JavaStrategy {

    private final Proof proof;

    protected JavaAbstractFeatureStrategy(Proof proof) {
        this.proof = proof;
    }

    /**
     * @return Returns the proof.
     */
    protected Proof getProof() {
        return proof;
    }

    /**
     * @param heuristics
     * @param thenFeature
     * @return the conditional feature return true when the rule belongs to one of the given
     *         heuristics
     */
    protected Feature ifHeuristics(String[] heuristics, Feature thenFeature) {
        return ConditionalFeature.createConditional(getFilterFor(heuristics), thenFeature);
    }

    protected Feature ifHeuristics(String[] heuristics, Feature thenFeature,
            Feature elseFeature) {
        return ConditionalFeature.createConditional(getFilterFor(heuristics), thenFeature,
            elseFeature);
    }

    protected Feature ifHeuristics(String[] names, int priority) {
        return ConditionalFeature.createConditional(getFilterFor(names), cost(priority), cost(0));
    }

    protected TacletFilter getFilterFor(String[] p_names) {
        ImmutableList<RuleSet> heur = ImmutableList.nil();
        for (int i = 0; i != p_names.length; ++i) {
            heur = heur.prepend(getHeuristic(p_names[i]));
        }
        return new IHTacletFilter(false, heur);
    }

    protected RuleSet getHeuristic(String p_name) {
        final NamespaceSet nss = getProof().getNamespaces();
        final Namespace<@NonNull RuleSet> ns = nss.ruleSets();
        final RuleSet h = ns.lookup(new Name(p_name));

        assert h != null : "Did not find the rule set " + p_name;

        return h;
    }

    /**
     * returns the service instance for access to {@link de.uka.ilkd.key.ldt.LDT}s
     *
     * @return the services for access to the meta logic
     */
    protected final Services getServices() {
        return getProof().getServices();
    }

}
