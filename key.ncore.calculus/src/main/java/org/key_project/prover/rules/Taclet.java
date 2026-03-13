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

import org.checkerframework.checker.calledmethods.qual.RequiresCalledMethods;
import org.checkerframework.checker.initialization.qual.UnderInitialization;
import org.checkerframework.checker.nullness.qual.EnsuresNonNull;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import static org.key_project.util.Strings.formatAsList;

/// A taclet (formerly known as schematic theory specific rule) is a rule representation used
/// within the KeY verification system.
public abstract class Taclet implements Rule {
    /// Annotations attached to taclets, specifying their kind, e.g., lemma.
    protected final ImmutableSet<TacletAnnotation> tacletAnnotations;

    /// unique name of the taclet
    protected final Name name;

    /// name displayed by the pretty printer
    protected final String displayName;

    /// contains the find term
    protected final @Nullable SyntaxElement find;

    /// The restriction(s) for applying this update. [ApplicationRestriction].
    protected final @NonNull ApplicationRestriction applicationRestriction;

    /// the <tt>assumes</tt> sequent of the taclet
    protected final Sequent assumesSequent;

    /// Variables that have to be created each time the taclet is applied. Those variables occur in
    /// the varcond part of a taclet description.
    protected final ImmutableList<? extends NewVarcond> varsNew;

    /// variables with a "x not free in y" variable condition. This means the instantiation of
    /// VariableSV x must not occur free in the instantiation of TermSV y.
    protected final ImmutableList<? extends NotFreeIn> varsNotFreeIn;

    /// variable conditions used to express that a termsv depends on the free variables of a given
    /// formula(SV) Used by skolemization rules.
    protected final ImmutableList<? extends NewDependingOn> varsNewDependingOn;

    /// Additional generic conditions for schema variable instantiations.
    protected final ImmutableList<? extends VariableCondition> variableConditions;

    /// the list of taclet goal descriptions
    protected final ImmutableList<TacletGoalTemplate> goalTemplates;

    /// the set of taclet options for this taclet
    protected final ChoiceExpr choices;

    /// map from a schemavariable to its prefix. The prefix is used to test correct instantiations
    /// of the schemavariables by resolving/avoiding collisions. Mainly the prefix consists of a
    /// list
    /// of all variables that may appear free in the instantiation of the schemavariable (a bit more
    /// complicated for rewrite taclets, see paper of M:Giese)
    protected final ImmutableMap<@NonNull SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap;

    /// cache; contains set of all bound variables
    protected @Nullable ImmutableSet<QuantifiableVariable> boundVariables = null;

    /// tracks state of pre-computation
    private boolean contextInfoComputed = false;
    private boolean contextIsInPrefix = false;

    protected @Nullable String tacletAsString;

    /// Set of schema variables of the `assumes` part
    protected @Nullable ImmutableSet<SchemaVariable> assumesVariables = null;

    /// list of rulesets (formerly known as heuristics) the taclet belongs to
    protected final ImmutableList<RuleSet> ruleSets;

    /// trigger of the taclet
    protected final @Nullable Trigger trigger;

    // The two rule engines for matching and execution (application) of taclets
    // In the long run, we should think about keeping those somewhere else, e.g., in the services
    // such that we gain more flexibility like combined matchers that do not just match one taclet
    // but all at once for a given term.

    /// The taclet matcher
    protected @NonNull TacletMatcher matcher;

    /// The taclet executor
    protected @NonNull TacletExecutor<? extends @NonNull ProofGoal<?>, ? extends @NonNull RuleApp> executor;

    /// creates a Taclet (originally known as Schematic Theory Specific Rules)
    ///
    /// @param name the name of the Taclet
    /// @param find the Term or Sequent that is the pattern that has to be found in a sequent and
    /// the places where it matches the Taclet can be applied
    /// @param applPart contains the application part of a Taclet that is the if-sequence, the
    /// variable conditions
    /// @param goalTemplates a list of goal descriptions.
    /// @param attrs attributes for the Taclet; these are boolean values indicating a noninteractive
    /// or recursive use of the Taclet.
    @EnsuresNonNull({ "matcher", "executor" })
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
        this.displayName = attrs.displayName();
        this.trigger = attrs.trigger();
        this.ruleSets = ruleSets;
        this.choices = choices;
        createTacletServices();
        check();
    }

    /// Throws an exception if the taclet is improperly constructed. This is the case if
    /// - There is no find part, but the application restriction does not match "in sequent state."
    /// - The find part is a sequent but contains no or more than one formula.
    private void check(@UnderInitialization Taclet this) {
        if (find == null
                && (applicationRestriction == null || // check to make checkerframework happy
                        !applicationRestriction.matches(ApplicationRestriction.IN_SEQUENT_STATE))) {
            throw new IllegalStateException("NoFind taclets should imply \\inSequentState");
        }
        if (find instanceof Sequent seq && seq.size() != 1) {
            throw new IllegalStateException(
                "Antec and Succ taclets must have exactly one formula in sequent");
        }
    }

    /// @return Whether the taclet has a trigger.
    public boolean hasTrigger() {
        return trigger != null;
    }

    public @Nullable Trigger getTrigger() {
        return trigger;
    }

    @RequiresCalledMethods(value = "this", methods = "createAndInitializeMatcher")
    public final TacletMatcher getMatcher() {
        return matcher;
    }

    /// creates and initializes the taclet matching and execution engines has to be called at the
    /// end
    /// of initialization
    @EnsuresNonNull({ "matcher", "executor" })
    private void createTacletServices(@UnderInitialization Taclet this) {
        createAndInitializeMatcher();
        createAndInitializeExecutor();
    }

    /// A helper method for creating the appropriate taclet matcher.
    @EnsuresNonNull("matcher")
    protected abstract void createAndInitializeMatcher(@UnderInitialization Taclet this);

    /// A helper method for creating the appropriate taclet executor.
    @EnsuresNonNull("executor")
    protected abstract void createAndInitializeExecutor(@UnderInitialization Taclet this);

    /// computes and returns all variables that occur bound in the taclet including the taclets
    /// defined in `addrules` sections. The result is cached and therefore only computed once.
    ///
    /// @return all variables occurring bound in the taclet
    public abstract ImmutableSet<QuantifiableVariable> getBoundVariables();

    /// collects bound variables in taclet entities others than goal templates
    ///
    /// @return set of variables that occur bound in taclet entities others than goal templates
    protected abstract ImmutableSet<QuantifiableVariable> getBoundVariablesHelper();

    /// returns true iff the taclet contains a "close goal"-statement
    ///
    /// @return true iff the taclet contains a "close goal"-statement
    public boolean closeGoal() {
        return goalTemplates.isEmpty();
    }

    /// looks if a variable is declared as new and returns its sort to match with or the schema
    /// variable it shares the match-sort with. Returns null if the SV is not declared to as new.
    ///
    /// @param var the SchemaVariable to look for
    /// @return the sort of the SV to match or the SV it shares the same match-sort with
    public @Nullable NewVarcond varDeclaredNew(SchemaVariable var) {
        for (final NewVarcond nv : varsNew) {
            if (nv.getSchemaVariable() == var) {
                return nv;
            }
        }
        return null;
    }

    /// @return the generic variable conditions of this taclet
    public ImmutableList<? extends VariableCondition> getVariableConditions() {
        return variableConditions;
    }

    /// @return the name of the Taclet
    @Override
    public @NonNull Name name() {
        return name;
    }

    /// @return the display name of the taclet, or, if not specified -- the canonical name
    @Override
    public @NonNull String displayName() {
        return displayName;
    }

    /// @return the assumes-sequence of the application part of the Taclet.
    public Sequent assumesSequent() {
        return assumesSequent;
    }

    /// @return the application restrictions of the Taclet.
    public ApplicationRestriction applicationRestriction() {
        return applicationRestriction;
    }

    /// @return an iterator over the variables that are new in the Taclet.
    public ImmutableList<? extends NewVarcond> varsNew() {
        return varsNew;
    }

    /// @return an iterator over the variable pairs that indicate that are new in the Taclet.
    public ImmutableList<? extends NotFreeIn> varsNotFreeIn() {
        return varsNotFreeIn;
    }

    public ImmutableList<? extends NewDependingOn> varsNewDependingOn() {
        return varsNewDependingOn;
    }

    /// @return an iterator over the goal descriptions.
    public ImmutableList<TacletGoalTemplate> goalTemplates() {
        return goalTemplates;
    }

    public ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap() {
        return prefixMap;
    }

    /// @return true if one of the goal templates is a replacewith. Already computed and cached by
    /// method cacheMatchInfo
    public boolean hasReplaceWith() {
        for (final TacletGoalTemplate goalTemplate : goalTemplates) {
            if (goalTemplate.replaceWithExpressionAsObject() != null) {
                return true;
            }
        }
        return false;
    }

    /// Returns the computed prefix for the given schemavariable. The prefix of a schemavariable is
    /// used to determine if an instantiation is correct, in more detail: it mainly contains all
    /// variables that can appear free in an instantiation of the schemvariable sv (rewrite taclets
    /// have some special handling, see paper of M. Giese and comment of method isContextInPrefix).
    ///
    /// @param sv the Schemavariable
    /// @return prefix of schema variable sv
    public @Nullable TacletPrefix getPrefix(SchemaVariable sv) {
        return prefixMap.get(sv);
    }

    public ChoiceExpr getChoices() {
        return choices;
    }

    /// @return an iterator over the rule sets.
    public Iterator<RuleSet> ruleSets() {
        return ruleSets.iterator();
    }

    /// Returns the set of schemavariables of the taclet's assumes-part
    ///
    /// @return Set of schemavariables of the `if` part
    protected abstract ImmutableSet<? extends SchemaVariable> getAssumesVariables();

    /// This method is used to determine if top level updates are allowed to be ignored. This is the
    /// case if we have an AntecTaclet or SuccTaclet but not for a RewriteTaclet
    ///
    /// @return true if top level updates shall be ignored
    public boolean ignoreTopLevelUpdates() {
        return find instanceof Sequent &&
                !applicationRestriction.matches(ApplicationRestriction.IN_SEQUENT_STATE);
    }

    /// Returns true iff a context flag is set in one of the entries in the prefix map. Is cached
    /// after having been called once. __OPTIMIZE__ is caching really necessary here?
    ///
    /// @return true iff a context flag is set in one of the entries in the prefix map.
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

    /// @return set of schemavariables of the `\assumes` and the (optional) `\find` part
    public abstract ImmutableSet<SchemaVariable> getAssumesAndFindVariables();

    /// Helper for {@link Taclet#toString()}, specifically the `assumes` part.
    protected StringBuffer toStringAssumes(StringBuffer sb) {
        if (!assumesSequent.isEmpty()) {
            sb.append("\\assumes (").append(assumesSequent).append(") ");
            sb.append("\n");
        }
        return sb;
    }

    /// Helper for {@link Taclet#toString()}, specifically the variable conditions.
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

    /// Helper for {@link Taclet#toString()}, specifically the goal templates.
    protected StringBuffer toStringGoalTemplates(StringBuffer sb) {
        if (goalTemplates.isEmpty()) {
            sb.append("\\closegoal");
        } else {
            sb.append(formatAsList(goalTemplates, "", ";\n", "\n"));
        }
        return sb;
    }

    /// Helper for {@link Taclet#toString()}, specifically the triggers.
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

    /// Helper for {@link Taclet#toString()}, specifically the attributes.
    StringBuffer toStringAttribs(StringBuffer sb) {
        // if (noninteractive()) sb = sb.append(" \\noninteractive");
        sb.append("\nChoices: ").append(choices);
        return sb;
    }

    /// Helper for {@link Taclet#toString()}, specifically the rule sets.
    protected StringBuffer toStringRuleSets(StringBuffer sb) {
        if (!ruleSets.isEmpty()) {
            sb.append("\\heuristics").append(formatAsList(ruleSets, "(", ", ", ")"));
        }
        return sb;
    }

    /// Returns a representation of the Taclet as String
    ///
    /// @return string representation
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

    @SuppressWarnings("unchecked")
    public @NonNull <G extends ProofGoal<@NonNull G>> TacletExecutor<@NonNull G, ?> getExecutor() {
        return (TacletExecutor<@NonNull G, ?>) executor;
    }

    public abstract Taclet setName(String name);

    public ImmutableList<RuleSet> getRuleSets() {
        return ruleSets;
    }

}
