/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractApp;
import de.uka.ilkd.key.scripts.meta.Option;

import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

public class DependencyContractCommand extends AbstractCommand {

    public DependencyContractCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "dependency";
    }

    @Override
    public void execute(ScriptCommandAst command) throws ScriptException, InterruptedException {

        Parameters arguments = state().getValueInjector().inject(new Parameters(), command);

        final Goal goal = state.getFirstOpenAutomaticGoal();

        if (arguments.heap == null) {
            Services services = goal.proof().getServices();
            arguments.heap = services.getTermFactory()
                    .createTerm(services.getTypeConverter().getHeapLDT().getHeap());
        }

        List<PosInOccurrence> pios = find(arguments.on, goal.sequent());

        if (pios.isEmpty()) {
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

    private List<PosInOccurrence> find(JTerm term, Sequent sequent) {
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

    private void find(List<PosInOccurrence> pios, JTerm term, PosInOccurrence pio) {
        Term subTerm = pio.subTerm();
        if (term.equals(subTerm)) {
            pios.add(pio);
        } else {
            ImmutableArray<? extends Term> subs = subTerm.subs();
            for (int i = 0; i < subs.size(); i++) {
                find(pios, term, pio.down(i));
            }
        }
    }

    private void apply(Goal goal, UseDependencyContractApp ruleApp, Parameters arguments) {
        JTerm on = arguments.on;
        JTerm[] subs = on.subs().toArray(new JTerm[0]);
        subs[0] = arguments.heap;
        Services services = goal.proof().getServices();
        JTerm replaced =
            services.getTermFactory().createTerm(on.op(), subs, on.boundVars(), on.getLabels());
        List<PosInOccurrence> pios = find(replaced, goal.sequent());
        ruleApp = ruleApp.setStep(pios.get(0));
        ruleApp = ruleApp.tryToInstantiateContract(services);
        goal.apply(ruleApp);
    }

    public static class Parameters {
        @Option(value = "on")
        public JTerm on;

        @Option(value = "heap")
        public @Nullable JTerm heap;
    }
}
