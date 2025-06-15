/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.executor.javadl.RewriteTacletExecutor;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.*;
import org.key_project.prover.rules.TacletPrefix;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.PIOPathIterator;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

/**
 * A RewriteTaclet represents a taclet, whose find can be matched against any term in the sequent no
 * matter where it occurs. The only constraint to be fulfilled is that the term matches the
 * structure described by the term of the find-part.
 */
public class RewriteTaclet extends FindTaclet {
    /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given parameters that represents a
     * rewrite rule.
     *
     * @param name the Name of the Taclet
     * @param applPart the TacletApplPart that contains the application part of an Taclet that is
     *        the if-sequent, the variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param ruleSets a list of rule sets for the Taclet
     * @param attrs the TacletAttributes; these are boolean values indicating a noninteractive or
     *        recursive use of the Taclet.
     * @param find the find term of the Taclet
     * @param prefixMap an ImmutableMap that contains the prefix for each
     *        SchemaVariable in the Taclet
     * @param choices the SetOf<Choices> to which this taclet belongs to
     */
    public RewriteTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            ImmutableList<RuleSet> ruleSets,
            TacletAttributes attrs, JTerm find,
            ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap,
            ChoiceExpr choices,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this(name, applPart, goalTemplates, ruleSets, attrs, find, prefixMap,
            choices, false, tacletAnnotations);
    }

    public RewriteTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            ImmutableList<RuleSet> ruleSets,
            TacletAttributes attrs, JTerm find,
            ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap,
            ChoiceExpr choices,
            boolean surviveSymbExec,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, ruleSets, attrs, find, prefixMap, choices,
            surviveSymbExec, tacletAnnotations);
    }

    @Override
    public JTerm find() {
        return (JTerm) find;
    }

    @Override
    protected void createAndInitializeExecutor() {
        this.executor = new RewriteTacletExecutor(this);
    }

    /**
     * the top level operator has to be a simultaneous update. This method checks if the assignment
     * pairs of the update contain free logic variables and gives a veto if positive
     *
     * @param t the Term to check
     * @return false if vetoing
     */
    private boolean veto(JTerm t) {
        return !t.freeVars().isEmpty();
    }

    /**
     * For taclets with <code>getSameUpdatePrefix ()</code>, collect the updates above
     * <code>p_pos</code> and add them to the update context of the instantiations object
     * <code>p_mc</code>.
     *
     * @return the new instantiations with the additional updates, or <code>null</code>, if program
     *         modalities appear above <code>p_pos</code>
     */
    public MatchConditions checkPrefix(
            PosInOccurrence p_pos,
            MatchConditions p_mc) {
        int polarity = p_pos.isInAntec() ? -1 : 1; // init polarity
        SVInstantiations svi = p_mc.getInstantiations();
        // this is assumed to hold
        assert p_pos.posInTerm() != null;

        PIOPathIterator it = p_pos.iterator();
        while (it.next() != -1) {
            final JTerm t = (JTerm) it.getSubTerm();
            var op = t.op();
            if (op instanceof Transformer) {
                return null;
            } else if (op instanceof UpdateApplication
                    && it.getChild() == UpdateApplication.targetPos()
                    && !applicationRestriction().equals(ApplicationRestriction.NONE)) {
                if (applicationRestriction().matches(ApplicationRestriction.IN_SEQUENT_STATE)
                        || veto(t)) {
                    return null;
                } else {
                    JTerm update = UpdateApplication.getUpdate(t);
                    svi = svi.addUpdate(update, t.getLabels());
                }
            } else if (!applicationRestriction().equals(ApplicationRestriction.NONE)
                    && (op instanceof JModality)) {
                return null;
            }

            if (polarity != 0) {
                polarity = polarity(op, it, polarity);
            }
        }

        if (applicationRestriction().equals(ApplicationRestriction.NONE)) {
            return p_mc;
        }
        if (applicationRestriction().matches(ApplicationRestriction.ANTECEDENT_POLARITY)
                && polarity != -1
                || applicationRestriction().matches(ApplicationRestriction.SUCCEDENT_POLARITY)
                        && polarity != 1) {
            return null;
        }
        return p_mc.setInstantiations(svi);
    }

    /**
     * Compute polarity
     *
     * (the {@code AntecSuccPrefixChecker} seems to reimplement this.
     */
    private int polarity(final Operator op, final PIOPathIterator it, int polarity) {
        // toggle polarity if find term is
        // subterm of
        if ((op == Junctor.NOT) || // not
                (op == Junctor.IMP && it.getChild() == 0)) { // left hand side of implication
            polarity = polarity * -1;
            // do not change polarity if find term
            // is subterm of
        } else if ((op == Junctor.AND) || // and
                (op == Junctor.OR) || // or
                (op == Junctor.IMP && it.getChild() != 0) || // right hand side of implication
                (op == IfThenElse.IF_THEN_ELSE && it.getChild() != 0)) { // then or else part of
                                                                         // if-then-else
            // do nothing
        } else { // find term has no polarity in any
                 // other case
            polarity = 0;
        }
        return polarity;
    }


    @Override
    protected StringBuffer toStringFind(StringBuffer sb) {
        StringBuffer res = super.toStringFind(sb);
        return res.append(applicationRestriction().toString());
    }

    public SequentFormula getRewriteResult(Goal goal, TermLabelState termLabelState,
            Services services, TacletApp app) {
        return ((RewriteTacletExecutor) getExecutor()).getRewriteResult(goal, termLabelState,
            services, app);
    }

    @Override
    public @NonNull RewriteTaclet setName(@NonNull String s) {
        final TacletApplPart applPart =
            new TacletApplPart(assumesSequent(), applicationRestriction(), varsNew(),
                varsNotFreeIn(),
                varsNewDependingOn(), getVariableConditions());
        final TacletAttributes attrs = new TacletAttributes(displayName(), trigger);

        return new RewriteTaclet(new Name(s), applPart, goalTemplates(), getRuleSets(), attrs,
            (JTerm) find,
            prefixMap, choices, getSurviveSymbExec(), tacletAnnotations);
    }
}
