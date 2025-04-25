/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import java.util.Iterator;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.conditions.NewDependingOn;
import org.key_project.prover.rules.conditions.NewVarcond;
import org.key_project.prover.rules.conditions.NotFreeIn;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

import static org.key_project.util.Strings.formatAsList;

/**
 * A taclet (formerly known as schematic theory specific rule) is a rule representation used
 * within the KeY verification system.
 */
public abstract class Taclet implements Rule {
    protected final ImmutableSet<TacletAnnotation> tacletAnnotations;

    /** unique name of the taclet */
    protected final Name name;

    /** name displayed by the pretty printer */
    protected final String displayName;

    /** contains the find term */
    protected final SyntaxElement find;

    protected final ApplicationRestriction applicationRestriction;

    /**
     * the <tt>assumes</tt> sequent of the taclet
     */
    protected final Sequent assumesSequent;

    /**
     * Variables that have to be created each time the taclet is applied. Those variables occur in
     * the varcond part of a taclet description.
     */
    protected final ImmutableList<? extends NewVarcond> varsNew;

    /**
     * variables with a "x not free in y" variable condition. This means the instantiation of
     * VariableSV x must not occur free in the instantiation of TermSV y.
     */
    protected final ImmutableList<? extends NotFreeIn> varsNotFreeIn;

    /**
     * variable conditions used to express that a termsv depends on the free variables of a given
     * formula(SV) Used by skolemization rules.
     */
    protected final ImmutableList<? extends NewDependingOn> varsNewDependingOn;

    /** Additional generic conditions for schema variable instantiations. */
    protected final ImmutableList<? extends VariableCondition> variableConditions;

    /**
     * the list of taclet goal descriptions
     */
    protected final ImmutableList<TacletGoalTemplate> goalTemplates;

    /** the set of taclet options for this taclet */
    protected final ChoiceExpr choices;

    /**
     * map from a schemavariable to its prefix. The prefix is used to test correct instantiations of
     * the schemavariables by resolving/avoiding collisions. Mainly the prefix consists of a list of
     * all variables that may appear free in the instantiation of the schemavariable (a bit more
     * complicated for rewrite taclets, see paper of M:Giese)
     */
    protected final ImmutableMap<@NonNull SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap;

    /** cache; contains set of all bound variables */
    protected ImmutableSet<QuantifiableVariable> boundVariables = null;

    /** tracks state of pre-computation */
    private boolean contextInfoComputed = false;
    private boolean contextIsInPrefix = false;

    protected String tacletAsString;

    /** Set of schema variables of the {@code assumes} part */
    protected ImmutableSet<SchemaVariable> assumesVariables = null;

    /**
     * list of rulesets (formerly known as heuristics) the taclet belongs to
     */
    protected final ImmutableList<RuleSet> ruleSets;

    /**
     * trigger of the taclet
     */
    protected final Trigger trigger;

    // The two rule engines for matching and execution (application) of taclets
    // In the long run, we should think about keeping those somewhere else, e.g., in the services
    // such that we gain more flexibility like combined matchers that do not just match one taclet
    // but all at once for a given term.

    /**
     * The taclet matcher
     */
    protected TacletMatcher matcher;

    /**
     * The taclet executor
     */
    protected TacletExecutor<? extends @NonNull ProofGoal<?>, ? extends @NonNull RuleApp> executor;

    /**
     * creates a Taclet (originally known as Schematic Theory Specific Rules)
     *
     * @param name the name of the Taclet
     * @param find the Term or Sequent that is the pattern that has to be found in a sequent and the
     *        places
     *        where it matches the Taclet can be applied
     * @param applPart contains the application part of a Taclet that is the if-sequence, the
     *        variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param attrs attributes for the Taclet; these are boolean values indicating a noninteractive
     *        or recursive use of the Taclet.
     */
    protected Taclet(Name name, SyntaxElement find, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            ImmutableList<RuleSet> ruleSets,
            TacletAttributes attrs,
            ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap, ChoiceExpr choices,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this.tacletAnnotations = tacletAnnotations;
        this.name = name;
        this.find = find;
        applicationRestriction = applPart.restriction();
        assumesSequent = applPart.assumesSequent();
        varsNew = applPart.varsNew();
        varsNotFreeIn = applPart.varsNotFreeIn();
        varsNewDependingOn = applPart.varsNewDependingOn();
        variableConditions = applPart.variableConditions();
        this.goalTemplates = goalTemplates;
        this.prefixMap = prefixMap;
        this.displayName = attrs.displayName() == null ? name.toString() : attrs.displayName();
        this.trigger = attrs.trigger();
        this.ruleSets = ruleSets;
        this.choices = choices;
        check();
    }

    private void check() {
        if (find == null
                && !applicationRestriction.matches(ApplicationRestriction.IN_SEQUENT_STATE)) {
            throw new IllegalStateException("NoFind taclets should imply \\inSequentState");
        }
        if (find instanceof Sequent seq && seq.size() != 1) {
            throw new IllegalStateException(
                "Antec and Succ taclets must have exactly one formula in sequent");
        }
    }

    public boolean hasTrigger() {
        return trigger != null;
    }

    public Trigger getTrigger() {
        return trigger;
    }

    public final TacletMatcher getMatcher() {
        return matcher;
    }

    /**
     * creates and initializes the taclet matching and execution engines has to be called at the end
     * of initialization
     */
    protected void createTacletServices() {
        createAndInitializeMatcher();
        createAndInitializeExecutor();
    }

    protected abstract void createAndInitializeMatcher();

    protected abstract void createAndInitializeExecutor();

    /**
     * computes and returns all variables that occur bound in the taclet including the taclets
     * defined in <tt>addrules</tt> sections. The result is cached and therefore only computed once.
     *
     * @return all variables occurring bound in the taclet
     */
    public abstract ImmutableSet<QuantifiableVariable> getBoundVariables();

    /**
     * collects bound variables in taclet entities others than goal templates
     *
     * @return set of variables that occur bound in taclet entities others than goal templates
     */
    protected abstract ImmutableSet<QuantifiableVariable> getBoundVariablesHelper();

    /**
     * returns true iff the taclet contains a "close goal"-statement
     *
     * @return true iff the taclet contains a "close goal"-statement
     */
    public boolean closeGoal() {
        return goalTemplates.isEmpty();
    }

    /**
     * looks if a variable is declared as new and returns its sort to match with or the schema
     * variable it shares the match-sort with. Returns null if the SV is not declared to as new.
     *
     * @param var the SchemaVariable to look for
     * @return the sort of the SV to match or the SV it shares the same match-sort with
     */
    public NewVarcond varDeclaredNew(SchemaVariable var) {
        for (final NewVarcond nv : varsNew) {
            if (nv.getSchemaVariable() == var) {
                return nv;
            }
        }
        return null;
    }

    /**
     * @return the generic variable conditions of this taclet
     */
    public ImmutableList<? extends VariableCondition> getVariableConditions() {
        return variableConditions;
    }

    /**
     * returns the name of the Taclet
     */
    @Override
    public @NonNull Name name() {
        return name;
    }

    /**
     * returns the display name of the taclet, or, if not specified -- the canonical name
     */
    @Override
    public @NonNull String displayName() {
        return displayName;
    }

    /**
     * returns the if-sequence of the application part of the Taclet.
     */
    public Sequent assumesSequent() {
        return assumesSequent;
    }

    /**
     * returns the application restrictions of the Taclet.
     */
    public ApplicationRestriction applicationRestriction() {
        return applicationRestriction;
    }

    /**
     * returns an iterator over the variables that are new in the Taclet.
     */
    public ImmutableList<? extends NewVarcond> varsNew() {
        return varsNew;
    }

    /**
     * returns an iterator over the variable pairs that indicate that are new in the Taclet.
     */
    public ImmutableList<? extends NotFreeIn> varsNotFreeIn() {
        return varsNotFreeIn;
    }

    public ImmutableList<? extends NewDependingOn> varsNewDependingOn() {
        return varsNewDependingOn;
    }

    /**
     * returns an iterator over the goal descriptions.
     */
    public ImmutableList<TacletGoalTemplate> goalTemplates() {
        return goalTemplates;
    }

    public ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap() {
        return prefixMap;
    }

    /**
     * returns true if one of the goal templates is a replacewith. Already computed and cached by
     * method cacheMatchInfo
     */
    public boolean hasReplaceWith() {
        for (final TacletGoalTemplate goalTemplate : goalTemplates) {
            if (goalTemplate.replaceWithExpressionAsObject() != null) {
                return true;
            }
        }
        return false;
    }

    /**
     * returns the computed prefix for the given schemavariable. The prefix of a schemavariable is
     * used to determine if an instantiation is correct, in more detail: it mainly contains all
     * variables that can appear free in an instantiation of the schemvariable sv (rewrite taclets
     * have some special handling, see paper of M. Giese and comment of method isContextInPrefix).
     *
     * @param sv the Schemavariable
     * @return prefix of schema variable sv
     */
    public TacletPrefix getPrefix(SchemaVariable sv) {
        return prefixMap.get(sv);
    }

    public ChoiceExpr getChoices() {
        return choices;
    }

    /** returns an iterator over the rule sets. */
    public Iterator<RuleSet> ruleSets() {
        return ruleSets.iterator();
    }

    /**
     * returns the set of schemavariables of the taclet's assumes-part
     *
     * @return Set of schemavariables of the {@code if} part
     */
    protected abstract ImmutableSet<? extends SchemaVariable> getAssumesVariables();

    /**
     * this method is used to determine if top level updates are allowed to be ignored. This is the
     * case if we have an AntecTaclet or SuccTaclet but not for a RewriteTaclet
     *
     * @return true if top level updates shall be ignored
     */
    public boolean ignoreTopLevelUpdates() {
        return !applicationRestriction.matches(ApplicationRestriction.IN_SEQUENT_STATE);
    }

    /**
     * returns true iff a context flag is set in one of the entries in the prefix map. Is cached
     * after having been called once. __OPTIMIZE__ is caching really necessary here?
     *
     * @return true iff a context flag is set in one of the entries in the prefix map.
     */
    public boolean isContextInPrefix() {
        if (contextInfoComputed) {
            return contextIsInPrefix;
        }
        contextInfoComputed = true;
        Iterator<TacletPrefix> it = prefixMap().valueIterator();
        while (it.hasNext()) {
            if (it.next().context()) {
                contextIsInPrefix = true;
                return true;
            }
        }
        contextIsInPrefix = false;
        return false;
    }

    /**
     * @return set of schemavariables of the {@code \assumes} and the (optional) {@code \find} part
     */
    public abstract ImmutableSet<SchemaVariable> getAssumesAndFindVariables();

    protected StringBuffer toStringAssumes(StringBuffer sb) {
        if (!assumesSequent.isEmpty()) {
            sb.append("\\assumes (").append(assumesSequent).append(") ");
            sb.append("\n");
        }
        return sb;
    }

    protected StringBuffer toStringVarCond(StringBuffer sb) {
        if (!varsNew.isEmpty() || !varsNotFreeIn.isEmpty() || !variableConditions.isEmpty()) {
            sb.append("\\varcond(");

            int countVarsNew = varsNew.size() - 1;
            for (final NewVarcond nvc : varsNew) {
                sb.append(nvc);
                if (countVarsNew > 0 || !varsNotFreeIn.isEmpty() || !variableConditions.isEmpty()) {
                    sb.append(", ");
                }
                --countVarsNew;
            }

            int countVarsNotFreeIn = varsNotFreeIn.size() - 1;
            for (NotFreeIn pair : varsNotFreeIn) {
                sb.append("\\notFreeIn(").append(pair.first()).append(", ")
                        .append(pair.second()).append(")");
                if (countVarsNotFreeIn > 0 || !variableConditions.isEmpty()) {
                    sb.append(", ");
                }
                --countVarsNotFreeIn;
            }

            sb.append(formatAsList(variableConditions, "", ", ", ""));

            sb.append(")\n");
        }
        return sb;
    }

    protected StringBuffer toStringGoalTemplates(StringBuffer sb) {
        if (goalTemplates.isEmpty()) {
            sb.append("\\closegoal");
        } else {
            sb.append(formatAsList(goalTemplates, "", ";\n", "\n"));
        }
        return sb;
    }

    protected StringBuffer toStringTriggers(StringBuffer sb) {
        if (trigger != null) {
            sb.append("\n\\trigger{");
            sb.append(trigger.triggerVar());
            sb.append("} ");
            sb.append(trigger.trigger());
            if (trigger.hasAvoidConditions()) {
                sb.append(" \\avoid ");
                sb.append(formatAsList(trigger.avoidConditions(), "", ", ", ""));
            }
        }
        return sb;
    }

    StringBuffer toStringAttribs(StringBuffer sb) {
        // if (noninteractive()) sb = sb.append(" \\noninteractive");
        sb.append("\nChoices: ").append(choices);
        return sb;
    }

    /**
     * returns a representation of the Taclet as String
     *
     * @return string representation
     */
    @Override
    public String toString() {
        if (tacletAsString == null) {
            // FIXME this essentially reimplements PrettyPrinter::printTaclet
            StringBuffer sb = new StringBuffer();
            sb.append(name()).append(" {\n");
            sb = toStringAssumes(sb);
            sb = toStringVarCond(sb);
            sb = toStringGoalTemplates(sb);
            sb = toStringRuleSets(sb);
            sb = toStringAttribs(sb);
            sb = toStringTriggers(sb);
            tacletAsString = sb.append("}").toString();
        }
        return tacletAsString;
    }

    protected StringBuffer toStringRuleSets(StringBuffer sb) {
        if (!ruleSets.isEmpty()) {
            sb.append("\\heuristics").append(formatAsList(ruleSets, "(", ", ", ")"));
        }
        return sb;
    }

    public @NonNull <G extends ProofGoal<@NonNull G>> TacletExecutor<@NonNull G, ?> getExecutor() {
        return (TacletExecutor<@NonNull G, ?>) executor;
    }

    public abstract Taclet setName(String s);

    public ImmutableList<RuleSet> getRuleSets() {
        return ruleSets;
    }

    public record ApplicationRestriction(int value) {
        public ApplicationRestriction {
            if ((value & ANTECEDENT_POLARITY) == ANTECEDENT_POLARITY
                    && (value & SUCCEDENT_POLARITY) == SUCCEDENT_POLARITY) {
                throw new IllegalArgumentException(
                    "Polarity cannot be antecedent and succedent at the same time");
            }
        }

        /** does not pose state restrictions on valid matchings */
        public static final ApplicationRestriction NONE = new ApplicationRestriction(0);
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
         * If the surrounding formula has been decomposed completely, the find-term will NOT appear
         * on
         * the succedent. The formula {@code wellformed(h)} in {@code wellformed(h) ==>} or in
         * {@code ==> wellformed(h) ->
         * (inv(h) = inv(h2))} or in {@code ==> \if(b) \then(!wellformed(h)) \else(!wellformed(h2))}
         * has
         * antecedent polarity. The formula {@code wellformed(h)} in
         * {@code wellformed(h) <-> wellformed(h2) ==>}
         * has NO antecedent polarity.
         * <br>
         * If this flag is set, the rule matches <b>only</b> on positions with antecedent polarity.
         */
        public static final int ANTECEDENT_POLARITY = 4;
        /**
         * If the surrounding formula has been decomposed completely, the find-term will NOT appear
         * on
         * the antecedent. The formula {@code wellformed(h)} in {@code==> wellformed(h)} or in
         * {@code wellformed(h) ->
         * (inv(h) = inv(h2)) ==>} or in
         * {@code \if(b) \then(!wellformed(h)) \else(!wellformed(h2)) ==>}
         * has
         * succedent polarity. The formula {@code wellformed(h)} in
         * {@code wellformed(h) <-> wellformed(h2) ==>} has
         * NO succedent polarity.
         * <br>
         * If this flag is set, the rule matches <b>only</b> on positions with succedent polarity.
         */
        public static final int SUCCEDENT_POLARITY = 8;

        public boolean matches(ApplicationRestriction o) {
            return (value() & o.value()) != 0;
        }

        public boolean matches(int value) {
            return (value() & value) != 0;
        }

        public ApplicationRestriction combine(ApplicationRestriction restriction) {
            return new ApplicationRestriction(this.value | restriction.value());
        }

        public ApplicationRestriction combine(int value) {
            return new ApplicationRestriction(this.value | value);
        }

        @Override
        public String toString() {
            String res = "";
            if (matches(SAME_UPDATE_LEVEL)) {
                res += "\\sameUpdateLevel";
            }
            if (matches(IN_SEQUENT_STATE)) {
                res += "\\inSequentState";
            }
            if (matches(ANTECEDENT_POLARITY)) {
                res += "\\antecedentPolarity";
            }
            if (matches(SUCCEDENT_POLARITY)) {
                res += "\\succedentPolarity";
            }
            return res;
        }
    }
}
