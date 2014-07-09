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

import javax.swing.KeyStroke;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.utilities.KeyStrokeManager;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.ui.UserInterface;

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

    ProofMacroListener pml;

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
        //
        // create the rule application engine
        final ApplyStrategy applyStrategy =
                new ApplyStrategy(mediator.getProfile().getSelectedGoalChooserBuilder().create());
        final Proof proof = mediator.getInteractiveProver().getProof();
        final UserInterface ui = mediator.getUI();

        //
        // set the max number of steps if given
        int oldNumberOfSteps = mediator.getMaxAutomaticSteps();
        if(getNumberSteps() > 0) {
            mediator.setMaxAutomaticSteps(getNumberSteps());
        } else {
            setNumberSteps(oldNumberOfSteps);
        }
        //
        // The observer to handle the progress bar
        final ProverTaskListener pbl = ui.addListener(this, goals.size());
        applyStrategy.addProverTaskObserver(pbl);

        //
        // inform the listener
        int goalsClosed = 0;
        long time = 0;
        int appliedRules = 0;
        ProofMacroFinishedInfo info =
                new ProofMacroFinishedInfo(this, goals, proof, time,
                                           appliedRules, goalsClosed);

        //
        // start actual autoprove
        try {
            for (Goal goal : goals) {
                Node node = goal.node();
                ApplyStrategyInfo result = applyStrategy.start(proof, goal);

                // retreat if not closed
                if(!node.isClosed()) {
                    proof.pruneProof(node);
                } else {
                    goalsClosed++;
                }

                // update statistics
                time += result.getTime();
                appliedRules += result.getAppliedRuleApps();
                info = new ProofMacroFinishedInfo(info, result);

                synchronized(applyStrategy) { // wait for applyStrategy to finish its last rule application
                   if(applyStrategy.hasBeenInterrupted()) { // only now reraise the interruption exception
                      throw new InterruptedException();
                   }
                }
            }
        } finally {
            // reset the old number of steps
            mediator.setMaxAutomaticSteps(oldNumberOfSteps);
            setNumberSteps(oldNumberOfSteps);
            applyStrategy.removeProverTaskObserver(pbl);
            ui.removeListener(this);
        }
        return info;
    }

    @Override
    public KeyStroke getKeyStroke () {
        return KeyStrokeManager.get(this);
    }
}