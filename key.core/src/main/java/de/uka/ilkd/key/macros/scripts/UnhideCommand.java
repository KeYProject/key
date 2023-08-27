/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.util.collection.ImmutableList;

/**
 * Proof script command to insert a formula hidden earlier in the proof.
 *
 * Usage:
 *
 * <pre>
 *     unhide "f1, f2 ==> f3, f4"
 * </pre>
 *
 * All formulas in the parameter sequent are re-added to the sequent.
 *
 * @author Mattias Ulbrich
 */
public class UnhideCommand extends AbstractCommand<UnhideCommand.Parameters> {

    public static final String INSERT_HIDDEN_PATTERN = "insert_hidden_taclet_[0-9]+";

    private static final TacletFilter FILTER = new TacletFilter() {
        @Override
        protected boolean filter(Taclet taclet) {
            return taclet.name().toString().matches(INSERT_HIDDEN_PATTERN);
        }
    };

    public UnhideCommand() {
        super(Parameters.class);
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override
    public void execute(Parameters args) throws ScriptException, InterruptedException {

        Goal goal = state.getFirstOpenAutomaticGoal();

        Set<Term> antes = new HashSet<>();
        args.sequent.antecedent().forEach(sf -> antes.add(sf.formula()));

        Set<Term> succs = new HashSet<>();
        args.sequent.succedent().forEach(sf -> succs.add(sf.formula()));

        RuleAppIndex index = goal.ruleAppIndex();
        ImmutableList<NoPosTacletApp> apps = index.getNoFindTaclet(FILTER, service);

        for (NoPosTacletApp app : apps) {
            SchemaVariable b = app.instantiations().svIterator().next();
            Object bInst = app.instantiations().getInstantiation(b);
            boolean succApp = app.taclet().goalTemplates().head().sequent().antecedent().isEmpty();
            if (succApp) {
                if (succs.contains(bInst)) {
                    goal.apply(app);
                }
            } else {
                if (antes.contains(bInst)) {
                    goal.apply(app);
                }
            }
        }
    }

    @Override
    public String getName() {
        return "unhide";
    }

    public static class Parameters {
        @Option("#2")
        public Sequent sequent;
    }

}
