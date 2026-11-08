/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.quantifierHeuristics.constraint;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;

import org.key_project.logic.Term;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * In KeY 1.x we supported a free variable calculus based on meta variables. This feature has been
 * abandoned in KeY 2.0. Until the strategy for quantifier instantiations is adapted, we cannot get
 * rid of them completely (they are used to determine triggers).
 */
@NullMarked
public class ConstraintAwareSyntacticalReplaceVisitor extends SyntacticalReplaceVisitor {

    @Deprecated
    private final Constraint metavariableInst;

    @SuppressWarnings("NullAway")
    public ConstraintAwareSyntacticalReplaceVisitor(TermLabelState termLabelState,
            Services services, Constraint metavariableInst,
            @Nullable PosInOccurrence applicationPosInOccurrence, @Nullable Rule rule,
            @Nullable RuleApp ruleApp, @Nullable TacletLabelHint labelHint) {
        // The constraint machinery runs without a rule/application context. The superclass stores
        // these arguments in nullable fields and only consults them conditionally, so the
        // historical contract of this constructor is that they may all be null. The super
        // constructor's parameters are not nullable; suppressed with a scoped key.
        super(termLabelState, labelHint, applicationPosInOccurrence, services, rule, ruleApp,
            false);
        this.metavariableInst = metavariableInst;
    }

    @Override
    protected Term toTerm(Term t) {
        if (!EqualityConstraint.metaVars(t, services).isEmpty() && !metavariableInst.isBottom()) {
            // use the visitor recursively for replacing metavariables that
            // might occur in the term (if possible)
            final ConstraintAwareSyntacticalReplaceVisitor srv =
                new ConstraintAwareSyntacticalReplaceVisitor(termLabelState, services,
                    metavariableInst, applicationPosInOccurrence, rule, ruleApp, labelHint);
            t.execPostOrder(srv);
            return srv.getTerm();
        } else {
            return t;
        }
    }

    public void visited(Term visited) {
        if (visited.op() instanceof Metavariable mv &&
                metavariableInst.getInstantiation(mv, services).op() != visited.op()) {
            pushNew(metavariableInst.getInstantiation(mv, services));
        } else {
            super.visit(visited);
        }
    }

}
