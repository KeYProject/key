/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.rules;

import java.util.Iterator;

import org.key_project.logic.Name;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.ncore.proof.ProofGoal;
import org.key_project.ncore.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.ncore.sequent.Sequent;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

import static org.key_project.util.Strings.formatAsList;

public abstract class Taclet<G extends @NonNull ProofGoal<G>, App extends @NonNull RuleApp<G, App>>
        implements Rule<G, App> {
    protected final ImmutableSet<TacletAnnotation> tacletAnnotations;

    /** unique name of the taclet */
    private final Name name;

    /** name displayed by the pretty printer */
    private final String displayName;

    /**
     * the <tt>if</tt> sequent of the taclet
     */
    private final Sequent assumesSequent;

    /**
     * Variables that have to be created each time the taclet is applied. Those variables occur in
     * the varcond part of a taclet description.
     */
    private final ImmutableList<NewVarcond> varsNew;
    /**
     * variables with a "x not free in y" variable condition. This means the instantiation of
     * VariableSV x must not occur free in the instantiation of TermSV y.
     */
    private final ImmutableList<NotFreeIn> varsNotFreeIn;
    /**
     * variable conditions used to express that a termsv depends on the free variables of a given
     * formula(SV) Used by skolemization rules.
     */
    private final ImmutableList<NewDependingOn> varsNewDependingOn;

    /** Additional generic conditions for schema variable instantiations. */
    private final ImmutableList<VariableCondition> variableConditions;

    /**
     * the list of taclet goal descriptions
     */
    private final ImmutableList<TacletGoalTemplate<G, App>> goalTemplates;

    /**
     * map from a schemavariable to its prefix. The prefix is used to test correct instantiations of
     * the schemavariables by resolving/avoiding collisions. Mainly the prefix consists of a list of
     * all variables that may appear free in the instantiation of the schemavariable (a bit more
     * complicated for rewrite taclets, see paper of M:Giese)
     */
    protected final ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap;

    /** cache; contains set of all bound variables */
    private ImmutableSet<QuantifiableVariable> boundVariables = null;

    /** tracks state of pre-computation */
    private boolean contextInfoComputed = false;
    private boolean contextIsInPrefix = false;

    protected String tacletAsString;

    /** Set of schemavariables of the {@code assumes} part */
    private ImmutableSet<SchemaVariable> assumesVariables = null;

    private final Trigger trigger;

    /* TODO: find better solution */
    private final boolean surviveSymbExec;

    /**
     * The taclet matcher
     */
    private TacletMatcher matcher;

    /**
     * The taclet executor
     */
    protected TacletExecutor<G, App, ? extends Taclet<G, App>> executor;

    /**
     * creates a Taclet (originally known as Schematic Theory Specific Rules)
     *
     * @param name the name of the Taclet
     * @param applPart contains the application part of a Taclet that is the if-sequence, the
     *        variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param attrs attributes for the Taclet; these are boolean values indicating a noninteractive
     *        or recursive use of the Taclet.
     */
    protected Taclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate<G, App>> goalTemplates,
            TacletAttributes attrs, ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap,
            boolean surviveSmbExec,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this.tacletAnnotations = tacletAnnotations;
        this.name = name;
        assumesSequent = applPart.assumesSequent();
        varsNew = applPart.varsNew();
        varsNotFreeIn = applPart.varsNotFreeIn();
        varsNewDependingOn = applPart.varsNewDependingOn();
        variableConditions = applPart.variableConditions();
        this.goalTemplates = goalTemplates;
        this.prefixMap = prefixMap;
        this.displayName = attrs.displayName() == null ? name.toString() : attrs.displayName();
        this.surviveSymbExec = surviveSmbExec;

        this.trigger = attrs.trigger();
    }

    public boolean hasTrigger() {
        return trigger != null;
    }

    public Trigger getTrigger() {
        return trigger;
    }

    public TacletMatcher getMatcher() {
        return matcher;
    }

    /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given parameters.
     *
     * @param name the name of the Taclet
     * @param applPart contains the application part of a Taclet that is the if-sequence, the
     *        variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param attrs attributes for the Taclet; these are boolean values indicating a noninteractive
     *        or recursive use of the Taclet.
     */
    protected Taclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate<G, App>> goalTemplates,
            TacletAttributes attrs, ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this(name, applPart, goalTemplates, attrs, prefixMap, false,
            tacletAnnotations);
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
     * @return all variables occuring bound in the taclet
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
    public ImmutableList<VariableCondition> getVariableConditions() {
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
    public String displayName() {
        return displayName;
    }

    /**
     * returns the if-sequence of the application part of the Taclet.
     */
    public Sequent assumesSequent() {
        return assumesSequent;
    }

    /**
     * returns an iterator over the variables that are new in the Taclet.
     */
    public ImmutableList<NewVarcond> varsNew() {
        return varsNew;
    }

    /**
     * returns an iterator over the variable pairs that indicate that are new in the Taclet.
     */
    public ImmutableList<NotFreeIn> varsNotFreeIn() {
        return varsNotFreeIn;
    }

    public ImmutableList<NewDependingOn> varsNewDependingOn() {
        return varsNewDependingOn;
    }

    /**
     * returns an iterator over the goal descriptions.
     */
    public ImmutableList<TacletGoalTemplate<G, App>> goalTemplates() {
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
        // TODO
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

    /**
     * returns the set of schemavariables of the taclet's assumes-part
     *
     * @return Set of schemavariables of the {@code if} part
     */
    protected abstract ImmutableSet<SchemaVariable> getAssumesVariables();

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

    StringBuffer toStringAssumes(StringBuffer sb) {
        if (!assumesSequent.isEmpty()) {
            sb.append("\\assumes (").append(assumesSequent).append(") ");
            sb.append("\n");
        }
        return sb;
    }

    StringBuffer toStringVarCond(StringBuffer sb) {
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

    StringBuffer toStringGoalTemplates(StringBuffer sb) {
        if (goalTemplates.isEmpty()) {
            sb.append("\\closegoal");
        } else {
            sb.append(formatAsList(goalTemplates, "", ";\n", "\n"));
        }
        return sb;
    }

    StringBuffer toStringTriggers(StringBuffer sb) {
        if (trigger != null) {
            sb.append("\n\\trigger{");
            sb.append(trigger.triggerVar());
            sb.append("} ");
            sb.append(trigger.getTerm());
            if (trigger.hasAvoidConditions()) {
                sb.append(" \\avoid ");
                sb.append(formatAsList(trigger.avoidConditions(), "", ", ", ""));
            }
        }
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
            sb = toStringTriggers(sb);
            tacletAsString = sb.append("}").toString();
        }
        return tacletAsString;
    }

    /**
     * applies the given rule application to the specified goal
     *
     * @param goal the goal that the rule application should refer to.
     * @param tacletApp the rule application that is executed.
     * @return List of the goals created by the rule which have to be proved. If this is a
     *         close-goal-taclet ( this.closeGoal () ), the first goal of the return list is the
     *         goal that should be closed (with the constraint this taclet is applied under).
     */
    @Override
    public @NonNull ImmutableList<G> apply(G goal, App tacletApp) {
        return getExecutor().apply(goal, tacletApp);
    }

    public TacletExecutor<G, App, ? extends Taclet<G, App>> getExecutor() {
        return executor;
    }

    public abstract Taclet<G, App> setName(String s);
}
