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


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;

/**
 * The Class TryCloseMacro tries to close goals. Goals are either closed or left
 * untouched.
 *
 * This uses the code provided by Michael Kirsten in
 * {@link InteractiveProver$AutoWorker}.
 *
 * The number of autosteps may be temporarily altered for this macro.
 *
 * @author mattias ulbrich
 */
public class TryCloseMacro extends AbstractProofMacro {

    /**
     * Instantiates a new try close macro.
     * No changes to the max number of steps.
     */
    public TryCloseMacro() {
    }

    /**
     * Instantiates a new try close macro.
     *
     * @param numberSteps
     *            the max number of steps. -1 means no change.
     */
    public TryCloseMacro(int numberSteps) {
        setNumberSteps(numberSteps);
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#getName()
     */
    @Override
    public String getName() {
        return "Close provable goals below";
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
    public boolean canApplyTo(KeYMediator mediator,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        return goals != null && !goals.isEmpty();
    }

    @Override
    public boolean isApplicableWithoutPosition() {
        return true;
    }
    
    /*
     * Run the automation on the goal. Retreat if not successful.
     */
    @Override
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
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
                new ApplyStrategy(mediator.getProfile().getSelectedGoalChooserBuilder().create());
        // assert: all goals have the same proof
        final Proof proof = goals.head().proof();

        //
        // set the max number of steps if given
        int oldNumberOfSteps = mediator.getMaxAutomaticSteps();
        if(getNumberSteps() > 0) {
            mediator.setMaxAutomaticSteps(getNumberSteps());
        } else {
            setNumberSteps(oldNumberOfSteps);
        }
        final ProofMacro macroAdapter = new SkipMacro() {
            @Override
            public String getName() { return ""; }
            @Override
            public String getDescription() { return "Anonymous macro"; }
        };
        macroAdapter.setNumberSteps(getNumberSteps());
        //
        // The observer to handle the progress bar
        final ProofMacroListener pml =  new ProgressBarListener(macroAdapter, goals.size(),
                                                                getNumberSteps(), listener);
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
                final ApplyStrategyInfo result = applyStrategy.start(proof, goal);
                //final Goal closedGoal;

                // retreat if not closed
                if(!node.isClosed()) {
                    proof.pruneProof(node);
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
            // reset the old number of steps
            mediator.setMaxAutomaticSteps(oldNumberOfSteps);
            setNumberSteps(oldNumberOfSteps);
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