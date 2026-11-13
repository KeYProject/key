/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.logic.Property;
import org.key_project.logic.Term;
import org.key_project.logic.Visitor;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

import org.jspecify.annotations.NonNull;

/// Feature for checking if the term of the first projection contains the term of the second
/// projection.
public class ContainsTermFeature implements Feature {
    /// Constant that represents the boolean value true
    public static final RuleAppCost ZERO_COST = NumberRuleAppCost.getZeroCost();

    /// Constant that represents the boolean value false
    public static final RuleAppCost TOP_COST = TopRuleAppCost.INSTANCE;

    private final ProjectionToTerm proj1;

    private final ProjectionToTerm proj2;

    private final Property<Term> eq;


    /// checks whether the second term is a subterm of the first one
    ///
    /// @param proj1 the ProjectionToTerm resolving to the term in which to search for the second
    /// term
    /// @param proj2 the ProjectionToTerm resolving to the term to be checked whether it is a
    /// subterm
    /// of the first one
    private ContainsTermFeature(ProjectionToTerm proj1, ProjectionToTerm proj2, Property<Term> eq) {
        this.proj1 = proj1;
        this.proj2 = proj2;
        this.eq = eq;
    }


    public static Feature create(ProjectionToTerm proj1, ProjectionToTerm proj2,
            Property<Term> eq) {
        return new ContainsTermFeature(proj1, proj2, eq);
    }


    @Override
    public <G extends ProofGoal<@NonNull G>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, G goal,
            MutableState mState) {
        final Term t1 = proj1.toTerm(app, pos, goal, mState);
        final Term t2 = proj2.toTerm(app, pos, goal, mState);
        assert t1 != null : "@AssumeAssertion(nullness): This is always the case";
        assert t2 != null : "@AssumeAssertion(nullness): This is always the case";
        ContainsTermVisitor visitor = new ContainsTermVisitor(t2, eq);
        t1.execPreOrder(visitor);
        if (visitor.found) {
            return ZERO_COST;
        } else {
            return TOP_COST;
        }
    }

    private static class ContainsTermVisitor implements Visitor<@NonNull Term> {
        boolean found = false;
        final Term term;
        final Property<Term> eq;

        public ContainsTermVisitor(Term term, Property<Term> eq) {
            this.term = term;
            this.eq = eq;
        }

        @Override
        public boolean visitSubtree(Term visited) {
            return true;
        }

        @Override
        public void visit(Term visited) {
            found = found || eq.equalsModThisProperty(visited, term);
        }

        @Override
        public void subtreeEntered(Term subtreeRoot) {
            // nothing to do
        }

        @Override
        public void subtreeLeft(Term subtreeRoot) {
            // nothing to do
        }
    }
}
