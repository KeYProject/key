package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.Varargs;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;
import org.key_project.util.collection.ImmutableList;

import java.util.Map;

public class RewriteCommand extends AbstractCommand<RewriteCommand.Parameters>{
    public RewriteCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "rewrite";
    }


    @Override public Parameters evaluateArguments(EngineState state,
                                                              Map<String, String> arguments) throws Exception {

        //TODO: check if find- and replace-terms are acceptable?
        Parameters p = state.getValueInjector()
                .inject(this, new Parameters(), arguments);
        return p;
    }

    @Override public void execute(AbstractUserInterfaceControl uiControl,
                                  Parameters args, EngineState state)
            throws ScriptException, InterruptedException {

        Proof proof = state.getProof();
        assert proof != null;

        //TODO: check if find term exists

        //number of find term in sequent
        int find_occ;

        boolean inAnect = true;

        //determine formula number of find term
        try {
            find_occ = state.getFirstOpenGoal().sequent().formulaNumberInSequent(inAnect, args.find);
        } catch (RuntimeException e1){
            try{
                inAnect = false;
                find_occ = state.getFirstOpenGoal().sequent().formulaNumberInSequent(inAnect, args.find);
            } catch (RuntimeException e2) {
                // find term not in sequent
                return;
            }
        }

        //TODO: find Taclet to transform find- into replace- term
        //ImmutableList<NoPosTacletApp> tacletlist = state.getFirstOpenGoal().indexOfTaclets().getRewriteTaclet();

        Taclet taclet;
        TacletApp tacletApp = null;



        Goal g = state.getFirstOpenGoal();
        g.apply(tacletApp);
        state.setGoal((Goal) null);
    }

    public static class Parameters {
        @Varargs(as = SequentFormula.class, prefix = "find")
        public SequentFormula find;
        @Varargs(as = SequentFormula.class, prefix = "replace")
        public SequentFormula replace;
    }
}

