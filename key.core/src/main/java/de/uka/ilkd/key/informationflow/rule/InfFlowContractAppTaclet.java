/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule;

import de.uka.ilkd.key.informationflow.rule.executor.InfFlowContractAppTacletExecutor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.RewriteTaclet;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.rules.TacletAnnotation;
import org.key_project.prover.rules.TacletApplPart;
import org.key_project.prover.rules.TacletAttributes;
import org.key_project.prover.rules.TacletPrefix;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;


/**
 * A normal RewriteTaclet except that the formula which is added by this taclet is also added to the
 * list of formulas contained in the INF_FLOW_CONTRACT_APPL_PROPERTY. The
 * INF_FLOW_CONTRACT_APPL_PROPERTY is used by the macros UseInformationFlowContractMacro and
 * PrepareInfFlowContractPreBranchesMacro to decide how to prepare the formulas resulting from
 * information flow contract applications.
 *
 * @author christoph
 */
public class InfFlowContractAppTaclet extends RewriteTaclet {

    public static final String USE_IF = "Use information flow contract for ";
    private static ImmutableSet<Name> alreadyRegistered = DefaultImmutableSet.nil();



    public static boolean hasType(Rule rule) {
        return rule != null && rule.name().toString().startsWith(USE_IF);
    }


    public static boolean registered(Name name) {
        return name != null && alreadyRegistered.contains(name);
    }


    public static void register(Name name) {
        alreadyRegistered = alreadyRegistered.add(name);
    }


    public static boolean unregister(Name name) {
        final boolean registered = registered(name);
        if (registered) {
            alreadyRegistered = alreadyRegistered.remove(name);
        }
        return registered;
    }


    public InfFlowContractAppTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            ImmutableList<RuleSet> ruleSets,
            TacletAttributes attrs, JTerm find,
            ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
            ChoiceExpr choices,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, ruleSets, attrs, find, prefixMap,
            choices, tacletAnnotations);
    }


    public InfFlowContractAppTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            ImmutableList<RuleSet> ruleSets,
            TacletAttributes attrs, JTerm find,
            ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
            ChoiceExpr choices, boolean surviveSymbExec,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, ruleSets, attrs, find, prefixMap,
            choices, surviveSymbExec, tacletAnnotations);
    }

    @Override
    protected void createAndInitializeExecutor() {
        executor = new InfFlowContractAppTacletExecutor(this);
    }

    @Override
    public @NonNull InfFlowContractAppTaclet setName(@NonNull String s) {
        final TacletApplPart applPart =
            new TacletApplPart(assumesSequent(), applicationRestriction(), varsNew(),
                varsNotFreeIn(),
                varsNewDependingOn(), getVariableConditions());
        final TacletAttributes attrs =
            new TacletAttributes(displayName(), trigger);

        return new InfFlowContractAppTaclet(new Name(s), applPart,
            goalTemplates(), getRuleSets(),
            attrs, (JTerm) find, prefixMap,
            choices, getSurviveSymbExec(),
            tacletAnnotations);
    }

}
