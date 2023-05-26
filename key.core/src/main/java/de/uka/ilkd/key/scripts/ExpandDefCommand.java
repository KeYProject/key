package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.scripts.meta.Option;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.BuiltInRuleAppIndex;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.meta.Option;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

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

        g.apply(completions.head());
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

        apps = apps.filter(it -> it instanceof PosTacletApp && it.posInOccurrence().subTerm().equals(p.on));

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
