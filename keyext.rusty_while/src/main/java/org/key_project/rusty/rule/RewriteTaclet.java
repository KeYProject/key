/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.rusty.logic.PIOPathIterator;
import org.key_project.rusty.logic.PosInOccurrence;
import org.key_project.rusty.logic.op.IfThenElse;
import org.key_project.rusty.logic.op.Junctor;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.UpdateApplication;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.executor.rustydl.RewriteTacletExecutor;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.rusty.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

/**
 * A RewriteTaclet represents a taclet, whose find can be matched against any term in the sequent no
 * matter where it occurs. The only constraint to be fulfilled is that the term matches the
 * structure described by the term of the find-part.
 */
public class RewriteTaclet extends FindTaclet {
    public enum ApplicationRestriction {
        /** does not pose state restrictions on valid matchings */
        None(0),
        /**
         * all taclet constituents must appear in the same state (and not below a modality (for
         * efficiency reasons))
         */
        SameUpdateLevel(1),
        /**
         * all taclet constituents must be in the same state as the sequent
         */
        InSequentState(2),
        /**
         * If the surrounding formula has been decomposed completely, the find-term will NOT appear
         * on
         * the SUCcedent. The formula {@code wellformed(h)} in {@code wellformed(h) ==>} or in
         * {@code ==> wellformed(h) ->
         * (inv(h) = inv(h2))} or in {@code ==> \if(b) \then(!wellformed(h)) \else(!wellformed(h2))}
         * has
         * antecedent polarity. The formula {@code wellformed(h)} in
         * {@code wellformed(h) <-> wellformed(h2) ==>}
         * has NO antecedent polarity.
         */
        AntecedentPolarity(4),
        /**
         * If the surrounding formula has been decomposed completely, the find-term will NOT appear
         * on
         * the ANTEcedent. The formula {@code wellformed(h)} in {@code==> wellformed(h)} or in
         * {@code wellformed(h) ->
         * (inv(h) = inv(h2)) ==>} or in
         * {@code \if(b) \then(!wellformed(h)) \else(!wellformed(h2)) ==>}
         * has
         * succedent polarity. The formula {@code wellformed(h)} in
         * {@code wellformed(h) <-> wellformed(h2) ==>} has
         * NO succedent polarity.
         */
        SuccedentPolarity(8);

        // TODO ask: This was final before but we need to change the value
        private int value;

        ApplicationRestriction(int value) {
            this.value = value;
        }

        int getValue() {
            return value;
        }

        public boolean matches(ApplicationRestriction o) {
            return (getValue() & o.getValue()) != 0;
        }

        // This is necessary for a passage in TacletPBuilder
        // Might work, but does not seem reasonable with an enum
        public void uniteRestrictions(ApplicationRestriction restriction) {
            this.value |= restriction.getValue();
        }
    }

    /**
     * encodes restrictions on the state where a rewrite taclet is applicable If the value is equal
     * to
     * <ul>
     * <li>{@link RewriteTaclet.ApplicationRestriction#None} no state restrictions are posed</li>
     * <li>{@link RewriteTaclet.ApplicationRestriction#SameUpdateLevel} then <code>\assumes</code>
     * must match on a
     * formula within the same state as <code>\find</code> rsp. <code>\add</code>. For efficiency no
     * modalities are allowed above the <code>\find</code> position</li>
     * <li>{@link RewriteTaclet.ApplicationRestriction#InSequentState} the <code>\find</code> part
     * is only allowed to
     * match on formulas which are evaluated in the same state as the sequent</li>
     * </ul>
     */
    private final ApplicationRestriction applicationRestriction;

    /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given parameters that represents a
     * rewrite rule.
     *
     * @param name the Name of the Taclet
     * @param applPart the TacletApplPart that contains the application part of a Taclet that is
     *        the if-sequent, the variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param attrs the TacletAttributes; these are boolean values indicating a noninteractive or
     *        recursive use of the Taclet.
     * @param find the find term of the Taclet
     * @param prefixMap an ImmutableMap that contains the prefix for each
     *        SchemaVariable in the Taclet
     * @param p_applicationRestriction an int defining state restrictions of the taclet (required
     *        for location check)
     */
    public RewriteTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            TacletAttributes attrs, Term find, ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
            ApplicationRestriction p_applicationRestriction,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this(name, applPart, goalTemplates, attrs, find, prefixMap,
            p_applicationRestriction, false, tacletAnnotations);
    }

    public RewriteTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            TacletAttributes attrs, Term find, ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
            ApplicationRestriction p_applicationRestriction, boolean surviveSymbExec,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, attrs, find, prefixMap,
            surviveSymbExec, tacletAnnotations);
        applicationRestriction = p_applicationRestriction;
        createTacletServices();
    }

    @Override
    protected void createAndInitializeExecutor() {
        this.executor = new RewriteTacletExecutor<>(this);
    }

    /**
     * this method is used to determine if top level updates are allowed to be ignored. This is the
     * case if we have an Antec or SuccTaclet but not for a RewriteTaclet
     *
     * @return true if top level updates shall be ignored
     */
    @Override
    public boolean ignoreTopLevelUpdates() {
        return false;
    }

    /**
     * returns the int encoding the kind of state restriction this rewrite taclet must obey
     *
     * @return the int encoding the kind of state restriction this rewrite taclet must obey
     */
    public ApplicationRestriction getApplicationRestriction() {
        return applicationRestriction;
    }


    /**
     * the top level operator has to be a simultaneous update. This method checks if the assignment
     * pairs of the update contain free logic variables and gives a veto if positive
     *
     * @param t the Term to check
     * @return false if vetoing
     */
    private boolean veto(Term t) {
        return !t.freeVars().isEmpty();
    }

    @Override
    protected StringBuffer toStringFind(StringBuffer sb) {
        StringBuffer res = super.toStringFind(sb);
        if (getApplicationRestriction().matches(ApplicationRestriction.SameUpdateLevel)) {
            res.append("\\sameUpdateLevel");
        }
        if (getApplicationRestriction().matches(ApplicationRestriction.InSequentState)) {
            res.append("\\inSequentState");
        }
        if (getApplicationRestriction().matches(ApplicationRestriction.AntecedentPolarity)) {
            res.append("\\antecedentPolarity");
        }
        if (getApplicationRestriction().matches(ApplicationRestriction.SuccedentPolarity)) {
            res.append("\\succedentPolarity");
        }
        return res;
    }

    @Override
    public RewriteTacletExecutor<? extends RewriteTaclet> getExecutor() {
        return (RewriteTacletExecutor<? extends RewriteTaclet>) executor;
    }

    @Override
    public RewriteTaclet setName(String s) {
        final TacletApplPart applPart = new TacletApplPart(ifSequent(), varsNew(), varsNotFreeIn(),
            varsNewDependingOn(), getVariableConditions());
        final TacletAttributes attrs = new TacletAttributes(displayName(), null);

        return new RewriteTaclet(new Name(s), applPart, goalTemplates(), attrs, find,
            prefixMap, applicationRestriction, tacletAnnotations);
    }

    public MatchConditions checkPrefix(PosInOccurrence p_pos, MatchConditions p_mc) {
        int polarity = p_pos.isInAntec() ? -1 : 1; // init polarity
        SVInstantiations svi = p_mc.getInstantiations();
        // this is assumed to hold
        assert p_pos.posInTerm() != null;

        PIOPathIterator it = p_pos.iterator();
        Operator op;
        while (it.next() != -1) {
            final Term t = it.getSubTerm();
            op = t.op();
            if (op instanceof UpdateApplication
                    && it.getChild() == UpdateApplication.targetPos()
                    && !getApplicationRestriction().matches(ApplicationRestriction.None)) {
                if (getApplicationRestriction().matches(ApplicationRestriction.InSequentState) || veto(t)) {
                    return null;
                } else {
                    Term update = UpdateApplication.getUpdate(t);
                    svi = svi.addUpdate(update);
                }
            } else if (!getApplicationRestriction().matches(ApplicationRestriction.None)
                    && (op instanceof Modality)) {
                return null;
            }

            if (polarity != 0) {
                polarity = polarity(op, it, polarity);
            }
        }

        if (getApplicationRestriction().matches(ApplicationRestriction.None)) {
            return p_mc;
        }
        if ((getApplicationRestriction().matches(ApplicationRestriction.AntecedentPolarity) && polarity != -1)
                || (getApplicationRestriction().matches(ApplicationRestriction.SuccedentPolarity) && polarity != 1)) {
            return null;
        }
        return p_mc.setInstantiations(svi);
    }

    /**
     * Compute polarity
     * <br>
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
}
