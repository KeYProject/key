package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.Set;

public class PropositionalMacro extends AbstractPropositionalExpansionMacro {

    private final int numSteps;

    private static final Set<String> ADMITTED_RULES_SET = asSet(
        "close",
        "closeAntec",
        "closeFalse",
        "closeTrue",
        "replace_known_left",
        "replace_known_right",
        "true_left",
        "false_right",
        "notLeft",
        "notRight",
        "impLeft",
        "doubleImpLeft",
        "impRight",
        "andLeft",
        "andRight",
        "orLeft",
        "orRight",
        "equiv_left",
        "equiv_right",
        "rotate_and",
        "rotate_or",
        "insert_eqv_once_lr",
        "insert_eqv_once_rl",
        "insert_eqv_lr",
        "insert_eqv_rl",
        "double_not",
        "concrete_not_1",
        "concrete_not_2",
        "concrete_impl_1",
        "concrete_impl_2",
        "concrete_impl_3",
        "concrete_impl_4",
        "concrete_and_1",
        "concrete_and_2",
        "concrete_and_3",
        "concrete_and_4",
        "concrete_or_1",
        "concrete_or_2",
        "concrete_or_3",
        "concrete_or_4",
        "concrete_or_5",
        "concrete_eq_2",
        "concrete_eq_3",
        "concrete_eq_4",
        "cut"
        );

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
                                          ImmutableList<Goal> goals, PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException {
        if (goals == null || goals.isEmpty()) {
            // should not happen, because in this case canApplyTo returns false
            return null;
        }

        // create the rule application engine
        final ProverCore applyStrategy =
            new ApplyStrategy(proof.getServices().getProfile().getSelectedGoalChooserBuilder().create());
        // assert: all goals have the same proof

        final ImmutableList<Goal> ignoredOpenGoals = setDifference(proof.openGoals(), goals);
        ProofMacroFinishedInfo info =
            new ProofMacroFinishedInfo(this, goals, proof, 0, 0, 0, false);

        //
        // start actual autoprove
        try {
            for (final Goal goal : goals) {
                Node node = goal.node();
                int maxSteps = numSteps > 0 ? numSteps : proof.getSettings().getStrategySettings().getMaxSteps();
                final ApplyStrategyInfo result =
                    applyStrategy.start(proof, ImmutableSLList.<Goal>nil().prepend(goal),
                        maxSteps, -1, false);
                //final Goal closedGoal;

                // retreat if not closed
                if(!node.isClosed()) {
                    proof.pruneProof(node);
                    //closedGoal = null;
                } else {
                    //closedGoal = goal;
                }

                synchronized(applyStrategy) { // wait for applyStrategy to finish its last rule application
                    info = new ProofMacroFinishedInfo(info, result);
                    if(applyStrategy.hasBeenInterrupted()) { // only now reraise the interruption exception
                        throw new InterruptedException();
                    }
                }
            }
        } finally {
            final ImmutableList<Goal> resultingGoals = setDifference(proof.openGoals(), ignoredOpenGoals);
            info = new ProofMacroFinishedInfo(this, info, resultingGoals);
        }
        return info;
    }

    public PropositionalMacro(int numSteps) {
        super();
        this.numSteps = numSteps;
    }



    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

    @Override
    protected boolean allowOSS() {
        return false;
    }

    @Override
    public String getName() {
        return "Propositional rules";
    }

    @Override
    public String getDescription() {
        return "This macro performs arbitrary propositional reasoning steps to close the goal.";
    }
}
