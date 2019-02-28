package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;

import java.util.*;

public class SMTCommand
        extends AbstractCommand<SMTCommand.SMTCommandArguments> {
    private static final Map<String, SolverType> SOLVER_MAP = computeSolverMap();

    public SMTCommand() {
        super(SMTCommandArguments.class);
    }

    private static Map<String, SolverType> computeSolverMap() {
        Map<String, SolverType> result = new HashMap<String, SolverType>();

        for (SolverType type : SolverType.ALL_SOLVERS) {
            result.put(type.getName(), type);
        }

        return Collections.unmodifiableMap(result);
    }

    @Override public SMTCommandArguments evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return ValueInjector.injection(this, new SMTCommandArguments(), arguments);
    }

    @Override public String getName() {
        return "smt";
    }

    @Override public void execute(SMTCommandArguments args)
            throws ScriptException, InterruptedException {
        SolverTypeCollection su = computeSolvers(args.solver);

        Goal goal = state.getFirstOpenAutomaticGoal();

        SMTSettings settings = new SMTSettings(
                goal.proof().getSettings().getSMTSettings(),
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                goal.proof());
        SolverLauncher launcher = new SolverLauncher(settings);
        Collection<SMTProblem> probList = new LinkedList<SMTProblem>();
        probList.add(new SMTProblem(goal));
        launcher.launch(su.getTypes(), probList, goal.proof().getServices());

        for (SMTProblem problem : probList) {
            if (problem.getFinalResult().isValid() == ThreeValuedTruth.VALID) {
                IBuiltInRuleApp app = RuleAppSMT.rule.createApp(null)
                        .setTitle(args.solver);
                problem.getGoal().apply(app);
            }
        }
    }

    private SolverTypeCollection computeSolvers(String value) {
        String[] parts = value.split(" *, *");
        List<SolverType> types = new ArrayList<SolverType>();
        for (String name : parts) {
            SolverType type = SOLVER_MAP.get(name);
            if (type != null) {
                types.add(type);
            }
        }
        return new SolverTypeCollection(value, 1, types);
    }

    static class SMTCommandArguments {
        @Option("solver")
        public String solver = "Z3";
    }

}
