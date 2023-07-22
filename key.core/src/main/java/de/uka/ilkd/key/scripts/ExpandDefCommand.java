package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.equality.TermLabelsProperty;
import de.uka.ilkd.key.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

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

        ImmutableList<TacletApp> completions = theApp.findIfFormulaInstantiations(g.sequent(), g.proof().getServices());
        if(completions == null || completions.isEmpty()) {
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
             apps = apps.prepend(g.ruleAppIndex().
                     getTacletAppAtAndBelow(FILTER, new PosInOccurrence(anteForm, PosInTerm.getTopLevel(), true), proof.getServices()));
        }

        for (SequentFormula succForm : g.sequent().succedent()) {
            apps = apps.prepend(g.ruleAppIndex().
                    getTacletAppAtAndBelow(FILTER, new PosInOccurrence(succForm, PosInTerm.getTopLevel(), false), proof.getServices()));
        }

        if (p.on != null) {
            apps = apps.filter(
                    it -> it instanceof PosTacletApp &&
                            ((JTerm)it.posInOccurrence().subTerm()).equalsModProperty(p.on, TermLabelsProperty.TERM_LABELS_PROPERTY));
        } else if (p.formula != null) {
            apps = apps.filter(
                    it -> it instanceof PosTacletApp &&
                            ((JTerm)it.posInOccurrence().sequentFormula().formula()).equalsModProperty(p.formula, TermLabelsProperty.TERM_LABELS_PROPERTY));
        } else {
            throw new ScriptException("Either 'formula' or 'on' must be specified");
        }


        if(apps.isEmpty()) {
            throw new ScriptException("There is no expansion rule app that matches 'on'");
        } else if(p.occ != null && p.occ >= 0) {
            if(p.occ >= apps.size()) {
                throw new ScriptException("The 'occ' parameter is beyond the number of occurrences.");
            }
            return apps.get(p.occ);
        } else {
            if(apps.size() != 1) {
                throw new ScriptException("The 'on' parameter is not unique");
            }
            return apps.head();
        }

    }

    public static class Parameters {
        @Option(value = "on")
        public @Nullable Term on;
        @Option(value = "occ")
        public @Nullable Integer occ;
        @Option(value = "formula")
        public @Nullable JTerm formula;

    }

    private static class ExpansionFilter extends TacletFilter {

        @Override
        protected boolean filter(Taclet taclet) {
            String name = taclet.name().toString();
            return  name.startsWith("Class_invariant_axiom_for") ||
                    name.startsWith("Definition_axiom_for");
        }
    }

}
