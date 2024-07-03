package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.BuiltInRuleAppIndex;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public class ExpandDefCommand extends AbstractCommand<ExpandDefCommand.Parameters> {

    private static final ExpansionFilter FILTER = new ExpansionFilter();

    public ExpandDefCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "expand";
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters args, EngineState state)
            throws ScriptException, InterruptedException {
        Goal g = state.getFirstOpenAutomaticGoal();
        TacletApp theApp = makeRuleApp(args, state);

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
                          it.posInOccurrence().subTerm().equalsModTermLabels(p.on));
        } else if (p.formula != null) {
            apps = apps.filter(
                    it -> it instanceof PosTacletApp &&
                          it.posInOccurrence().sequentFormula().formula().equalsModTermLabels(p.formula));
        } else {
            throw new ScriptException("Either 'formula' or 'on' must be specified");
        }

        if (apps.size() == 0) {
            throw new ScriptException("There is no matching expansion rule");
        } else if (p.occ >= 0) {
            if (p.occ >= apps.size()) {
                throw new ScriptException(
                    "The 'occ' parameter is beyond the number of occurrences.");
            }
            return apps.get(p.occ);
        } else {
            if (apps.size() != 1) {
                throw new ScriptException("The application is not uniquely identified");
            }
            return apps.head();
        }

    }

    public static class Parameters {
        @Option(value = "on", required = false)
        public Term on;
        @Option(value = "occ", required = false)
        public int occ = -1;
        @Option(value = "formula", required = false)
        public Term formula;
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
