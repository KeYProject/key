// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.strategy.StrategyProperties;

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
public class TryCloseMacro implements ProofMacro {

    /**
     * The max number of steps to be applied.
     * A value of -1 means no changes.
     */
    private final int numberSteps;

    /**
     * Instantiates a new try close macro.
     * No changes to the max number of steps.
     */
    public TryCloseMacro() {
        this.numberSteps = -1;
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
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#getDescription()
     */
    @Override
    public String getDescription() {
        return "Closes closable goals, leave rest untouched (see settings AutoPrune). " +
                "Applies only to goals beneath the selected node.";
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#canApplyTo(de.uka.ilkd.key.gui.KeYMediator, de.uka.ilkd.key.logic.PosInOccurrence)
     */
    @Override
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        return true;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#applyTo(de.uka.ilkd.key.gui.KeYMediator, de.uka.ilkd.key.logic.PosInOccurrence)
     */
    @Override
    public void applyTo(final KeYMediator mediator, PosInOccurrence posInOcc) {

        final Proof proof = mediator.getInteractiveProver().getProof();
        final StrategySettings strategySettings = proof.getSettings().getStrategySettings();

        // this returns a clone of the actual settings, ...
        final StrategyProperties properties =
                strategySettings.getActiveStrategyProperties();

        final String oldRetreatMode =
                properties.getProperty(StrategyProperties.RETREAT_MODE_OPTIONS_KEY);

        final int oldNumberSteps =
                mediator.getMaxAutomaticSteps();

        //
        // activate retreat mode
        properties.put(StrategyProperties.RETREAT_MODE_OPTIONS_KEY,
                StrategyProperties.RETREAT_MODE_RETREAT);

        // ... we only had a clone, so we need to replace the original settings.
        strategySettings.setActiveStrategyProperties(properties);

        //
        // set the max number of steps if given
        if(numberSteps > 0) {
            mediator.setMaxAutomaticSteps(numberSteps);
        }

        //
        // start actual autoprove
        Node invokedNode = mediator.getSelectedNode();
        ImmutableList<Goal> enabledGoals = proof.getSubtreeEnabledGoals(invokedNode);
        mediator.startAutoMode(enabledGoals);

        mediator.addAutoModeListener(new AutoModeListener() {

            @Override
            public void autoModeStopped(ProofEvent e) {
                // set retreat mode back to old value
                properties.put(StrategyProperties.RETREAT_MODE_OPTIONS_KEY, oldRetreatMode);
                strategySettings.setActiveStrategyProperties(properties);

                // reset the number of steps to old value
                mediator.setMaxAutomaticSteps(oldNumberSteps);

                // listener has done its job. remove it.
                mediator.removeAutoModeListener(this);
            }

            @Override
            public void autoModeStarted(ProofEvent e) {
            }
        });

    }

}
