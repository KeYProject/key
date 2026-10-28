/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.rule;

import de.uka.ilkd.key.informationflow.rule.executor.InfFlowContractAppTacletExecutor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.RewriteTaclet;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.rules.TacletAnnotation;
import org.key_project.prover.rules.TacletApplPart;
import org.key_project.prover.rules.TacletAttributes;
import org.key_project.prover.rules.TacletPrefix;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * A normal RewriteTaclet except that the formula which is added by this taclet is also added to the
 * list of formulas contained in the INF_FLOW_CONTRACT_APPL_PROPERTY. The
 * INF_FLOW_CONTRACT_APPL_PROPERTY is used by the macros UseInformationFlowContractMacro and
 * PrepareInfFlowContractPreBranchesMacro to decide how to prepare the formulas resulting from
 * information flow contract applications.
 *
 * @author christoph
 */
@NullMarked
public class InfFlowContractAppTaclet extends RewriteTaclet {

    public static final String USE_IF = "Use information flow contract for ";

    public static boolean hasType(@Nullable Rule rule) {
        return rule != null && rule.name().toString().startsWith(USE_IF);
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

    /**
     * The abstract declaration in the prover Taclet root declares
     * {@code createAndInitializeExecutor} with an {@code @UnderInitialization}
     * receiver, while the intermediate RewriteTaclet override (which is not
     * annotated) has an initialized implicit receiver. An explicit receiver on
     * this override cannot satisfy both: javac requires the concrete class
     * receiver (making EISOP report a mismatch with the initialized
     * intermediate), while an inherited default receiver mismatches the
     * under-initialized root declaration. The executor is constructed and
     * assigned exactly like RewriteTaclet does after all fields the executor
     * reads are set, so the receiver state carries no nullness risk.
     */
    @SuppressWarnings("nullness:override.receiver.invalid")
    @Override
    protected void createAndInitializeExecutor() {
        executor = new InfFlowContractAppTacletExecutor(this);
    }

    @Override
    public @NonNull InfFlowContractAppTaclet setName(@NonNull String s) {
        final ApplicationRestriction restriction = applicationRestriction();
        if (restriction == null) {
            throw new NullPointerException(
                "No application restriction for renaming the information flow contract taclet.");
        }
        final JTerm findTerm = (JTerm) find;
        if (findTerm == null) {
            throw new NullPointerException(
                "No find part for renaming the information flow contract taclet.");
        }
        final TacletApplPart applPart =
            new TacletApplPart(assumesSequent(), restriction, varsNew(),
                varsNotFreeIn(),
                varsNewDependingOn(), getVariableConditions());
        final TacletAttributes attrs =
            new TacletAttributes(displayName(), trigger);

        return new InfFlowContractAppTaclet(new Name(s), applPart,
            goalTemplates(), getRuleSets(),
            attrs, findTerm, prefixMap,
            choices, getSurviveSymbExec(),
            tacletAnnotations);
    }

}
