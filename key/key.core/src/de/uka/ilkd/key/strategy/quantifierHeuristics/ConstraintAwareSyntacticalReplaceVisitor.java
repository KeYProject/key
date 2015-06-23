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


/**
 * In KeY 1.x we supported a free variable calculus based on meta variables. 
 * This feature has been abandoned in KeY 2.0. Until the strategy for 
 * quantifier instantiations is adapted, we cannot get rid of them 
 * completely (they are used to determine triggers).
 */
public class ConstraintAwareSyntacticalReplaceVisitor extends
        SyntacticalReplaceVisitor {

    @Deprecated
    private final Constraint metavariableInst;

    public ConstraintAwareSyntacticalReplaceVisitor(
            TermLabelState termLabelState, Services services,
            Constraint metavariableInst,
            PosInOccurrence applicationPosInOccurrence, Rule rule, RuleApp ruleApp,
            TacletLabelHint labelHint, Goal goal) {
        super(termLabelState, services,
                applicationPosInOccurrence, rule, ruleApp, labelHint, goal);
        this.metavariableInst = metavariableInst;
    }
    
    protected Term toTerm(Term t) {
        if ( EqualityConstraint.metaVars (t).size () != 0 && !metavariableInst.isBottom () ) {
            // use the visitor recursively for replacing metavariables that
            // might occur in the term (if possible)
            final ConstraintAwareSyntacticalReplaceVisitor srv =
                    new ConstraintAwareSyntacticalReplaceVisitor (termLabelState, services, metavariableInst, 
                            applicationPosInOccurrence, rule, ruleApp, labelHint, goal);
            t.execPostOrder ( srv );
            return srv.getTerm ();
        } else {
            return t;
        }
    }

    public void visited(Term visited) {
        if (visited.op() instanceof Metavariable
                && metavariableInst.getInstantiation((Metavariable) visited.op(), services)
                        .op() != visited.op()) {
            pushNew(metavariableInst.getInstantiation((Metavariable) visited.op(), services));
        } else {
            super.visit(visited);
        }        
    }
    
}
