/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;

import org.key_project.logic.Term;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;


/**
 * In KeY 1.x we supported a free variable calculus based on meta variables. This feature has been
 * abandoned in KeY 2.0. Until the strategy for quantifier instantiations is adapted, we cannot get
 * rid of them completely (they are used to determine triggers).
 */
public class ConstraintAwareSyntacticalReplaceVisitor extends SyntacticalReplaceVisitor {

    @Deprecated
    private final Constraint metavariableInst;

    public ConstraintAwareSyntacticalReplaceVisitor(TermLabelState termLabelState,
            Services services, Constraint metavariableInst,
            PosInOccurrence applicationPosInOccurrence, Rule rule, RuleApp ruleApp,
            TacletLabelHint labelHint) {
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
