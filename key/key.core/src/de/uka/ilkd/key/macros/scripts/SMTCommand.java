package de.uka.ilkd.key.macros.scripts;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.SolverTypeCollection;

public class SMTCommand extends AbstractCommand {

    private static final String DEFAULT_SOLVER = "Z3";
    private static final String SOLVER_KEY = "solver";

    private static final Map<String, SolverType> SOLVER_MAP = computeSolverMap();

    @Override
    public String getName() {
        return "smt";
    }

    private static Map<String, SolverType> computeSolverMap() {
        Map<String, SolverType> result = new HashMap<String, SolverType>();

        for (SolverType type : SolverType.ALL_SOLVERS) {
            result.put(type.getName(), type);
        }

        return Collections.unmodifiableMap(result);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> state) throws ScriptException, InterruptedException {


        String value = args.get(SOLVER_KEY);
        if(value == null ) {
            value = DEFAULT_SOLVER;
        }

        SolverTypeCollection su = computeSolvers(value);

        Goal goal = getFirstOpenGoal(proof, state);

        SMTSettings settings = new SMTSettings(goal.proof().getSettings().getSMTSettings(),
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),goal.proof());
        SolverLauncher launcher = new SolverLauncher(settings);
        Collection<SMTProblem> probList = new LinkedList<SMTProblem>();
        probList.add(new SMTProblem(goal));
        launcher.launch(su.getTypes(), probList, goal.proof().getServices());

        for (SMTProblem problem : probList) {
            if (problem.getFinalResult().isValid() == ThreeValuedTruth.VALID) {
                IBuiltInRuleApp app = RuleAppSMT.rule.createApp(null).setTitle(value);
                problem.getGoal().apply(app);
            }
        }
    }

    private SolverTypeCollection computeSolvers(String value) {
        String[] parts = value.split(" *, *");
        List<SolverType> types = new ArrayList<SolverType>();
        for (String name : parts) {
            SolverType type = SOLVER_MAP.get(name);
            if(type != null) {
                types.add(type);
            }
        }
        return new SolverTypeCollection(value, 1, types);
    }

}
