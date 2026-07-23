/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.meta.Documentation;
import de.uka.ilkd.key.scripts.meta.Option;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/// The `expand` command applies expansion rules to definitions and class invariants.
/// It expands occurrences of definition axioms or class invariant axioms in the current sequent.
///
/// ## Usage Examples
/// - `expand on="someTerm"` - Expands definitions matching the term pattern
/// - `expand formula="x > 0" occ=1` - Expands the first occurrence in the specified formula
///
/// @author Mattias Ulbrich
@Documentation(category = "Fundamental", value = """
        The `expand` command applies expansion rules to definitions and class invariants.
        It finds and applies expansion taclets that match Definition_axiom_for or
        Class_invariant_axiom_for patterns in the current sequent.

        This is useful for unfolding definitions during proof construction.

        #### Usage Examples
        - `expand on="someTerm"` - Expands definitions matching the term pattern
        - `expand formula="x > 0" occ=1` - Expands the first occurrence in the specified formula
        """)
public class ExpandDefCommand extends AbstractCommand {

    private static final ExpansionFilter FILTER = new ExpansionFilter();

    public ExpandDefCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "expand";
    }

    @Override
    public void execute(ScriptCommandAst command) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), command);
        Goal g = state().getFirstOpenAutomaticGoal();
        TacletApp theApp = makeRuleApp(args, state());

        ImmutableList<TacletApp> completions =
            theApp.findIfFormulaInstantiations(g.sequent(), g.proof().getServices());
        if (completions == null || completions.isEmpty()) {
            throw new ScriptException("Cannot complete the rule app");
        }

        TacletApp app = completions.head();
        app = app.tryToInstantiate(g.proof().getServices().getOverlay(g.getLocalNamespaces()));
        if (app == null || !app.complete()) {
            throw new ScriptException("Cannot complete the rule app");
        }

        g.apply(app);

    }

    private TacletApp makeRuleApp(Parameters p, EngineState state) throws ScriptException {

        Goal g = state.getFirstOpenAutomaticGoal();
        Proof proof = state.getProof();

        ImmutableList<TacletApp> apps = ImmutableList.of();
        for (SequentFormula anteForm : g.sequent().antecedent()) {
            apps = apps.prepend(g.ruleAppIndex().getTacletAppAtAndBelow(FILTER,
                new PosInOccurrence(anteForm, PosInTerm.getTopLevel(), true), proof.getServices()));
        }

        for (SequentFormula succForm : g.sequent().succedent()) {
            apps = apps.prepend(g.ruleAppIndex().getTacletAppAtAndBelow(FILTER,
                new PosInOccurrence(succForm, PosInTerm.getTopLevel(), false),
                proof.getServices()));
        }

        if (p.on != null) {
            apps = apps.filter(
                it -> it instanceof PosTacletApp &&
                        p.on.matches(it.posInOccurrence()));
        } else if (p.formula != null) {
            apps = apps.filter(
                it -> it instanceof PosTacletApp &&
                        p.formula.matchesToplevel(it.posInOccurrence().sequentFormula()));
        } else {
            throw new ScriptException("Either 'formula' or 'on' must be specified");
        }

        if (apps.isEmpty()) {
            throw new ScriptException("There is no expansion rule app that matches 'on'");
        } else if (p.occ != null && p.occ >= 0) {
            if (p.occ >= apps.size()) {
                throw new ScriptException(
                    "The 'occ' parameter is beyond the number of occurrences.");
            }
            return apps.get(p.occ);
        } else {
            if (apps.size() != 1) {
                throw new ScriptException("The 'on' parameter is not unique");
            }
            return apps.head();
        }

    }

    public static class Parameters {
        @Option(value = "on")
        @Documentation("A term pattern to match the expansion location against")
        public @Nullable TermWithHoles on;
        @Option(value = "occ")
        @Documentation("The occurrence number when multiple matches exist (starts at 0)")
        public @Nullable Integer occ;
        @Option(value = "formula")
        @Documentation("A top-level formula in which to search for the expansion location")
        public @Nullable TermWithHoles formula;

    }

    private static class ExpansionFilter extends TacletFilter {

        @Override
        protected boolean filter(Taclet taclet) {
            String name = taclet.name().toString();
            return name.startsWith("Class_invariant_axiom_for") ||
                    name.startsWith("Definition_axiom_for");
        }
    }

}
