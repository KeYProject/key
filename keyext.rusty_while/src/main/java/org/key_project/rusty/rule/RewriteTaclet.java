/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.executor.javadl.RewriteTacletExecutor;
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

        private final int value;

        ApplicationRestriction(int value) {
            this.value = value;
        }

        int getValue() {
            return value;
        }

        public boolean matches(ApplicationRestriction o) {
            return (getValue() & o.getValue()) != 0;
        }

        // TODO ask:
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
     * @param applPart the TacletApplPart that contains the application part of an Taclet that is
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
}
