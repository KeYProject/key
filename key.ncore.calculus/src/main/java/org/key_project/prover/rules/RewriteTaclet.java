package org.key_project.prover.rules;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.PIOPathIterator;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

/**
 * A RewriteTaclet represents a taclet, whose find can be matched against any term in the sequent no
 * matter where it occurs. The only constraint to be fulfilled is that the term matches the
 * structure described by the term of the find-part.
 */
public abstract class RewriteTaclet extends FindTaclet {
    /** does not pose state restrictions on valid matchings */
    public static final int NONE = 0;

    /**
     * all taclet constituents must appear in the same state (and not below a modality (for
     * efficiency reasons))
     */
    public static final int SAME_UPDATE_LEVEL = 1;

    /**
     * all taclet constituents must be in the same state as the sequent
     */
    public static final int IN_SEQUENT_STATE = 2;

    /**
     * If the surrounding formula has been decomposed completely, the find-term will NOT appear on
     * the SUCcedent. The formula {@code wellformed(h)} in {@code wellformed(h) ==>} or in
     * {@code ==> wellformed(h) ->
     * (inv(h) = inv(h2))} or in {@code ==> \if(b) \then(!wellformed(h)) \else(!wellformed(h2))} has
     * antecedent polarity. The formula {@code wellformed(h)} in
     * {@code wellformed(h) <-> wellformed(h2) ==>}
     * has NO antecedent polarity.
     */
    public static final int ANTECEDENT_POLARITY = 4;

    /**
     * If the surrounding formula has been decomposed completely, the find-term will NOT appear on
     * the ANTEcedent. The formula {@code wellformed(h)} in {@code ==> wellformed(h)} or in
     * {@code wellformed(h) ->
     * (inv(h) = inv(h2)) ==>} or in {@code \if(b) \then(!wellformed(h)) \else(!wellformed(h2)) ==>}
     * has
     * succedent polarity. The formula {@code wellformed(h)} in
     * {@code wellformed(h) <-> wellformed(h2) ==>} has
     * NO succedent polarity.
     */
    public static final int SUCCEDENT_POLARITY = 8;

    /**
     * encodes restrictions on the state where a rewrite taclet is applicable If the value is equal
     * to
     * <ul>
     * <li>{@link RewriteTaclet#NONE} no state restrictions are posed</li>
     * <li>{@link RewriteTaclet#SAME_UPDATE_LEVEL} then <code>\assumes</code> must match on a
     * formula within the same state as <code>\find</code> rsp. <code>\add</code>. For efficiency no
     * modalities are allowed above the <code>\find</code> position</li>
     * <li>{@link RewriteTaclet#IN_SEQUENT_STATE} the <code>\find</code> part is only allowed to
     * match on formulas which are evaluated in the same state as the sequent</li>
     * </ul>
     */
    private final int applicationRestriction;

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
     * @param p_applicationRestriction an int defining state restrictions of the taclet (required
     *        for location check)
     * @param choices the SetOf<Choices> to which this taclet belongs to
     */
    public RewriteTaclet(Name name, TacletApplPart applPart,
                         ImmutableList<TacletGoalTemplate> goalTemplates,
                         ImmutableList<RuleSet> ruleSets,
                         TacletAttributes attrs, Term find,
                         ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap,
                         int p_applicationRestriction, ChoiceExpr choices,
                         ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this(name, applPart, goalTemplates, ruleSets, attrs, find, prefixMap,
                p_applicationRestriction, choices, false, tacletAnnotations);
    }

    public RewriteTaclet(Name name, TacletApplPart applPart,
                         ImmutableList<TacletGoalTemplate> goalTemplates,
                         ImmutableList<RuleSet> ruleSets,
                         TacletAttributes attrs, Term find,
                         ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap,
                         int p_applicationRestriction, ChoiceExpr choices,
                         boolean surviveSymbExec,
                         ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, ruleSets, attrs, find, prefixMap, choices,
                surviveSymbExec, tacletAnnotations);
        applicationRestriction = p_applicationRestriction;
        createTacletServices();
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
    public int getApplicationRestriction() {
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
        if ((getApplicationRestriction() & SAME_UPDATE_LEVEL) != 0) {
            res.append("\\sameUpdateLevel");
        }
        if ((getApplicationRestriction() & IN_SEQUENT_STATE) != 0) {
            res.append("\\inSequentState");
        }
        if ((getApplicationRestriction() & ANTECEDENT_POLARITY) != 0) {
            res.append("\\antecedentPolarity");
        }
        if ((getApplicationRestriction() & SUCCEDENT_POLARITY) != 0) {
            res.append("\\succedentPolarity");
        }
        return res;
    }
}
