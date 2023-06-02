package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractApp;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class DependencyContractCommand extends AbstractCommand<DependencyContractCommand.Parameters> {

    public DependencyContractCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "dependency";
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        Parameters args = new Parameters();
        state.getValueInjector().inject(this, args, arguments);
        return args;
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters arguments,
            EngineState state) throws ScriptException, InterruptedException {

        final Goal goal = state.getFirstOpenAutomaticGoal();

        if (arguments.heap == null) {
            Services services = goal.proof().getServices();
            arguments.heap = services.getTermFactory().createTerm(services.getTypeConverter().getHeapLDT().getHeap());
        }

        List<PosInOccurrence> pios = find(arguments.on, goal.sequent());

        if(pios.isEmpty()) {
            throw new ScriptException("dependency contract not applicable.");
        } else if (pios.size() > 1) {
            throw new ScriptException("no unique application");
        }

        PosInOccurrence pio = pios.get(0);
        ImmutableList<IBuiltInRuleApp> builtins = goal.ruleAppIndex().getBuiltInRules(goal, pio);
        for (IBuiltInRuleApp builtin : builtins) {
            if (builtin instanceof UseDependencyContractApp) {
                apply(goal, (UseDependencyContractApp) builtin, arguments);
            }
        }

    }

    private List<PosInOccurrence> find(Term term, Sequent sequent) {
        List<PosInOccurrence> pios = new ArrayList<>();
        for (SequentFormula sf : sequent.antecedent()) {
            PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), true);
            find(pios, term, pio);
        }

        for (SequentFormula sf : sequent.succedent()) {
            PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), false);
            find(pios, term, pio);
        }
        return pios;
    }

    private void find(List<PosInOccurrence> pios, Term term, PosInOccurrence pio) {
        Term subTerm = pio.subTerm();
        if (term.equals(subTerm)) {
            pios.add(pio);
        } else {
            ImmutableArray<Term> subs = subTerm.subs();
            for (int i = 0; i < subs.size(); i++) {
                find(pios, term, pio.down(i));
            }
        }
    }

    private void apply(Goal goal, UseDependencyContractApp ruleApp, Parameters arguments) {
        Term on = arguments.on;
        Term[] subs = on.subs().toArray(new Term[0]);
        subs[0] = arguments.heap;
        Services services = goal.proof().getServices();
        Term replaced = services.getTermFactory().createTerm(on.op(), subs, on.boundVars(), on.javaBlock(), on.getLabels());
        List<PosInOccurrence> pios = find(replaced, goal.sequent());
        ruleApp = ruleApp.setStep(pios.get(0));
        ruleApp = ruleApp.tryToInstantiateContract(services);
        goal.apply(ruleApp);
    }

    public static class Parameters {
        @Option(value = "on", required = true)
        public Term on;

        @Option(value = "heap", required = false)
        public Term heap;
    }
}
