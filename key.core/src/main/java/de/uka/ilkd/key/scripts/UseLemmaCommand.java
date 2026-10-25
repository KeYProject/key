/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.meta.Argument;
import de.uka.ilkd.key.scripts.meta.Documentation;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.Taclet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.proof.rulefilter.TacletFilter;

import java.util.List;
import java.util.NoSuchElementException;

/**
 * The command object CutCommand has as scriptcommand name "cut" As parameters: a formula with the
 * id "#2"
 */
public class UseLemmaCommand extends AbstractCommand {
    private static final Name INTRO_TACLET_NAME = new Name("intro");

    public UseLemmaCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "use_lemma";
    }

    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), arguments);
        execute(state(), args);
    }

    static void execute(EngineState state, Parameters args) throws ScriptException {
        de.uka.ilkd.key.rule.Taclet intro = state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(INTRO_TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(intro);

        // Explicitly instantiate skolem with the concrete sort of the term (e.g., boolean),
        // then instantiate schema variable "t" with the provided term.
        var services = state.getProof().getServices();
        SchemaVariable sk = getSV(app, "sk");
        SchemaVariable t = getSV(app, "t");

        // Use a deterministic name for the skolem; the specific name is not important here.
        app = app.createSkolemConstant("use_lemma_sk", sk, args.term.sort(), true, services);
        app = app.addCheckedInstantiation(t, args.term, services, true);

        // Apply the intro rule (adds equality to antecedent)
        Goal goalAfterIntro = state.getFirstOpenAutomaticGoal();
        ImmutableList<Goal> afterIntro = goalAfterIntro.apply(app);
        Goal workGoal = afterIntro.head();

        // Identify the added equality sequent formula and apply the Contract_axiom_for_* taclet on the left-hand term
        SequentFormula eqFormula = workGoal.sequent().getFormulaByNr(1);
        var posLeftTerm = new PosInOccurrence(eqFormula, PosInTerm.getTopLevel().down(0), true);

        // Query taclet apps at/below the method call position that start with "Contract_axiom_for_"
        var index = workGoal.ruleAppIndex();
        TacletFilter contractAxiomFilter = new TacletFilter() {
            @Override
            protected boolean filter(Taclet taclet) {
                return taclet.name().toString().startsWith("Contract_axiom_for_");
            }
        };
        var matchingApps = index.getTacletAppAtAndBelow(contractAxiomFilter, posLeftTerm, services);
        if (matchingApps.isEmpty()) {
            throw new ScriptException("No applicable Contract_axiom_for_* rule found at the lemma/method call term.");
        }
        TacletApp contractApp = matchingApps.head();
        var completedContractApp = contractApp.tryToInstantiate(services);
        if (completedContractApp != null) {
            contractApp = completedContractApp;
        }
        ImmutableList<Goal> afterContract = workGoal.apply(contractApp);

        // Hide the equality we introduced
        if (afterContract != null && !afterContract.isEmpty()) {
            for (Goal g2 : afterContract) {
                try {
                    SequentFormula changed = identifyAddedOrModifiedSequentFormula(g2);
                    hideAntecedentFormula(g2, changed);
                } catch (Exception ignore) {
                    // best-effort hiding; skip if not identifiable
                }
            }
        } else {
            hideAntecedentFormula(workGoal, eqFormula);
        }
    }

    private static SchemaVariable getSV(TacletApp app, String name) throws ScriptException {
        for (SchemaVariable sv : app.uninstantiatedVars()) {
            if (sv.name().toString().equals(name)) {
                return sv;
            }
        }
        throw new ScriptException("intro taclet: schema variable '" + name + "' not found");
    }

    // Determine which sequent formula got added or modified by the last step on this goal
    private static SequentFormula identifyAddedOrModifiedSequentFormula(Goal goal) {
        var changes = goal.node().getNodeInfo().getSequentChangeInfo().getSemisequentChangeInfo(false);
        var added = changes.addedFormulas();
        if (!added.isEmpty()) {
            return added.get(0);
        }
        var modified = changes.modifiedFormulas();
        if (!modified.isEmpty()) {
            return modified.get(0).newFormula();
        }
        throw new NoSuchElementException("Cannot identify added or modified sequent formula after intro.");
    }

    private static void hideAntecedentFormula(Goal g, SequentFormula toHide) {
        // hide_left applies to antecedent
        var tac = g.proof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(new Name("hide_left"));
        var pio = new PosInOccurrence(toHide, PosInTerm.getTopLevel(), true);
        TacletApp app = PosTacletApp.createPosTacletApp((FindTaclet) tac, SVInstantiations.EMPTY_SVINSTANTIATIONS, pio,
                g.proof().getServices());
        // instantiate the single schema variable of hide rule with the full formula
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        app = app.addCheckedInstantiation(sv, (JTerm) toHide.formula(), g.proof().getServices(), true);
        g.apply(app);
    }

    @Documentation(category = "Fundamental", value = """
            The cut command makes a case distinction (a cut) on a formula on the current proof goal.
            From within JML scripts, the alias 'assert' is more common than using 'cut'.
            If followed by a `\\by proof` suffix in JML, it refers the sequent where
            the cut formula is introduced to the succedent (i.e. where it is to be established).
            """)
    public static class Parameters {
        @Argument
        @Documentation("The lemma to invoke")
        public @MonotonicNonNull JTerm term;
    }

}
