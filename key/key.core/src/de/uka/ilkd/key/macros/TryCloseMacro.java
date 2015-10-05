// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.macros;


import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;

/**
 * The Class TryCloseMacro tries to close goals. Goals are either closed or left
 * untouched.
 *
 * This uses the code provided by Michael Kirsten in
 * {@link InteractiveProver$AutoWorker}.
 *
 * Unlike many macros, this macros has got a parameter ({@link #numberSteps}), such
 * that several instances of the class may exist with different semantics.
 *
 * The number of autosteps may be temporarily altered for this macro.
 *
 * @author mattias ulbrich
 */
public class TryCloseMacro extends AbstractProofMacro {

    private static class TryCloseProgressBarListener extends ProgressBarListener {

        private int notClosedGoals = 0;

        private TryCloseProgressBarListener(String name, int numberGoals, int numberSteps, ProverTaskListener l) {
            super(name, numberGoals, numberSteps, l);
        }

        public TryCloseProgressBarListener(int numberGoals, int numberSteps, ProverTaskListener listener) {
            super(numberGoals, numberSteps, listener);
        }

        @Override
        protected String getMessageSuffix() {
            if(notClosedGoals == 0) {
            return super.getMessageSuffix();
            } else {
                return super.getMessageSuffix() + ", " + notClosedGoals + " goal(s) remain(s) open.";
        }
        }

        private void incrementNotClosedGoals() {
            notClosedGoals++;
        }

    }

    /**
     * The max number of steps to be applied.
     * A value of -1 means no changes.
     *
     * This value may differ between instances of this class;
     */
    private final int numberSteps;

    /**
     * Instantiates a new try close macro.
     * No changes to the max number of steps.
     */
    public TryCloseMacro() {
        this(-1);
    }

    /**
     * Instantiates a new try close macro.
     *
     * @param numberSteps
     *            the max number of steps. -1 means no change.
     */
    public TryCloseMacro(int numberSteps) {
        this.numberSteps = numberSteps;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#getName()
     */
    @Override
    public String getName() {
        return "Close provable goals below";
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.macros.AbstractProofMacro#getScriptCommandName()
     */
    @Override
    public String getScriptCommandName() {
        return "tryclose";
    }

    /*
     * (non-Javadoc)
     * @see de.uka.ilkd.key.macros.ProofMacro#getCategory()
     */
    @Override
    public String getCategory() {
        return null;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#getDescription()
     */
    @Override
    public String getDescription() {
        return "Closes closable goals, leave rest untouched (see settings AutoPrune). " +
                "Applies only to goals beneath the selected node.";
    }

    /*
     * This macro is always applicable.
     */
    @Override
    public boolean canApplyTo(Proof proof,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        return goals != null && !goals.isEmpty();
    }

    /*
     * Run the automation on the goal. Retreat if not successful.
     */
    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          Proof proof,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException {
        if (goals == null || goals.isEmpty()) {
            // should not happen, because in this case canApplyTo returns
            // false
            return null;
        }

        //
        // create the rule application engine
        final ApplyStrategy applyStrategy =
                new ApplyStrategy(proof.getServices().getProfile().getSelectedGoalChooserBuilder().create());
        // assert: all goals have the same proof

        //
        // The observer to handle the progress bar
        final TryCloseProgressBarListener pml =  new TryCloseProgressBarListener(goals.size(),
                                                                numberSteps, listener);
        final ImmutableList<Goal> ignoredOpenGoals =
                setDifference(proof.openGoals(), goals);
        applyStrategy.addProverTaskObserver(pml);

        //
        // inform the listener
        ProofMacroFinishedInfo info =
                new ProofMacroFinishedInfo(this, goals, proof, 0, 0, 0);

        //
        // start actual autoprove
        try {
            for (final Goal goal : goals) {
                Node node = goal.node();
                int maxSteps = numberSteps > 0 ? numberSteps : proof.getSettings().getStrategySettings().getMaxSteps();
                final ApplyStrategyInfo result =
                      applyStrategy.start(proof, ImmutableSLList.<Goal>nil().prepend(goal),
                            maxSteps, -1, false);
                //final Goal closedGoal;

                // retreat if not closed
                if(!node.isClosed()) {
                    proof.pruneProof(node);
                    pml.incrementNotClosedGoals();
                    //closedGoal = null;
                } else {
                    //closedGoal = goal;
                }

                synchronized(applyStrategy) { // wait for applyStrategy to finish its last rule application
                    // update statistics
                    /*if (closedGoal == null) { TODO: This incremental approach would be nicer, but
                     *                                  therefore the comparison of Goal needs to be fixed.
                        info = new ProofMacroFinishedInfo(info, result);
                    } else {
                        info = new ProofMacroFinishedInfo(info, result,
                                                          info.getGoals().removeFirst(closedGoal));
                    }*/
                    info = new ProofMacroFinishedInfo(info, result);
                    if(applyStrategy.hasBeenInterrupted()) { // only now reraise the interruption exception
                        throw new InterruptedException();
                    }
                }
            }
        } finally {
            applyStrategy.removeProverTaskObserver(pml);
            final ImmutableList<Goal> resultingGoals =
                    setDifference(proof.openGoals(), ignoredOpenGoals);
            info = new ProofMacroFinishedInfo(this, info, resultingGoals);
        }
        return info;
    }

    private static ImmutableList<Goal> setDifference(ImmutableList<Goal> goals1,
                                                     ImmutableList<Goal> goals2) {
        ImmutableList<Goal> difference = goals1;
        for (Goal goal : goals2) {
            difference = difference.removeFirst(goal);
        }
        return difference;
    }
}