/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;

import org.jspecify.annotations.NonNull;


/**
 * In KeY 1.x we supported a free variable calculus based on meta variables. This feature has been
 * abandoned in KeY 2.0. Until the strategy for quantifier instantiations is adapted, we cannot get
 * rid of them completely (they are used to determine triggers).
 */
public class ConstraintAwareSyntacticalReplaceVisitor extends SyntacticalReplaceVisitor {

    @Deprecated
    private final Constraint metavariableInst;

    public ConstraintAwareSyntacticalReplaceVisitor(@NonNull TermLabelState termLabelState,
            @NonNull Services services, Constraint metavariableInst,
            @NonNull PosInOccurrence applicationPosInOccurrence, @NonNull Rule rule,
            @NonNull RuleApp ruleApp,
            @NonNull TacletLabelHint labelHint, @NonNull Goal goal) {
        super(termLabelState, labelHint, applicationPosInOccurrence, goal, rule, ruleApp, services,
            services.getTermBuilder(false));
        this.metavariableInst = metavariableInst;
    }

    protected @NonNull Term toTerm(Term t) {
        if (!EqualityConstraint.metaVars(t, services).isEmpty() && !metavariableInst.isBottom()) {
            // use the visitor recursively for replacing metavariables that
            // might occur in the term (if possible)
            final ConstraintAwareSyntacticalReplaceVisitor srv =
                new ConstraintAwareSyntacticalReplaceVisitor(termLabelState, services,
                    metavariableInst, applicationPosInOccurrence, rule, ruleApp, labelHint, goal);
            t.execPostOrder(srv);
            return srv.getTerm();
        } else {
            return t;
        }
    }

    public void visited(@NonNull Term visited) {
        if (visited.op() instanceof Metavariable mv &&
                metavariableInst.getInstantiation(mv, services).op() != visited.op()) {
            pushNew(metavariableInst.getInstantiation(mv, services));
        } else {
            super.visit(visited);
        }
    }

}
