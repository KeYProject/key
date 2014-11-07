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
import de.uka.ilkd.key.core.TaskFinishedInfo;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

/**
 * The interface ProofMacro is the entry point to a general strategy extension
 * system.
 *
 * <h3>Idea</h3>
 *
 * Doing interaction with KeY is often tedious, many steps have to be performed
 * over and over again. To facilitate the interaction, this frameworks allows a
 * developer to define "macro strategy steps" which combine many individual
 * steps and are helpful in an interactive verification attempt.
 *
 * This interface is kept deliberately separate from many of the other
 * mechanisms to remain open on how to implement the macro.
 *
 * <h3>Usage</h3>
 *
 * Proof macros are meant to be stateless singletons.
 *
 * Whenever a situation arises where the user wants to apply macros, they are
 * asked whether they can be applied (
 * {@link #canApplyTo(KeYMediator, PosInOccurrence)}). A macro is offered to the
 * user iff it returns <code>true</code>. No changes should be made there.
 *
 * A macro is then applied using {@link #applyTo(KeYMediator, PosInOccurrence)}.
 * This may change the proof by applying rule applications. It is allowed to use
 * automatic runs, manual instantiations, ...
 *
 * A proof macro needs to extract all necessary information on the application
 * from the mediator passed to the
 * {@link #applyTo(KeYMediator, PosInOccurrence)} (or
 * {@link #canApplyTo(KeYMediator, PosInOccurrence)}) method. You will be able
 * to access any interesting data from that starting point, especially
 * {@link KeYMediator#getInteractiveProver()}.
 *
 * <h3>Registration</h3>
 *
 * When implementing a new proof macro, no existing code needs to be adapted.
 * Please add the class name of your new implementation to the file
 * <tt>resources/META-INF/services/de.uka.ilkd.key.macros.ProofMacro</tt>.
 *
 * @see KeYMediator
 *
 * @author mattias ulbrich
 */
public interface ProofMacro {

    public void setNumberSteps(int numberSteps);

    public int getNumberSteps();

    /**
     * Gets the name of this macro.
     *
     * Used as menu entry
     *
     * @return a non-<code>null</code> constant string
     */
    public String getName();

    /**
     * Gets the description of this macro.
     *
     * Used as tooltip.
     *
     * @return a non-<code>null</code> constant string
     */
    public String getDescription();

    /**
     * Can this macro be applied?
     * 
     * This method should not make any changes but check if the macro can be
     * applied or not in the given context.
     * 
     * This method may be called from within the GUI thread and be compatible
     * with that fact.
     * 
     * @param mediator
     *            the mediator (not <code>null</code>)
     * @param posInOcc
     *            the position in occurrence (may be <code>null</code>)
     * 
     * @return <code>true</code>, if the macro is allowed to be applied
     */
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc);

    /**
     * Can this macro be applied on the given goals?
     *
     * This method should not make any changes but check if the macro can be
     * applied or not on the given goals.
     *
     * This method may be called from within the GUI thread and be compatible
     * with that fact.
     *
     * @param mediator
     *            the mediator (not <code>null</code>)
     * @param goals
     *            the goals (not <code>null</code>)
     * @param posInOcc
     *            the position in occurrence (may be <code>null</code>)
     *
     * @return <code>true</code>, if the macro is allowed to be applied
     */
    public boolean canApplyTo(KeYMediator mediator,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc);

    /**
     * Can this macro be applied on the given node?
     *
     * This method should not make any changes but check if the macro can be
     * applied or not on the given node.
     *
     * This method may be called from within the GUI thread and be compatible
     * with that fact.
     *
     * @param mediator
     *            the mediator (not <code>null</code>)
     * @param node
     *            the node (not <code>null</code>)
     * @param posInOcc
     *            the position in occurrence (may be <code>null</code>)
     *
     * @return <code>true</code>, if the macro is allowed to be applied
     */
    public boolean canApplyTo(KeYMediator mediator,
                              Node node,
                              PosInOccurrence posInOcc);
    
    /**
     * Can this macro be applied with no {@link PosInOccurrence} given?
     * This method is necessary because we need to check global applicability
     * even when no proof is loaded (e.g., in GUI initialization).
     * Fixes bug #1495
     */
    public boolean isApplicableWithoutPosition();

    /**
     * Apply this macro.
     * 
     * This method can change the proof by applying rules to it.
     * 
     * This method is usually called from a dedicated thread and not the GUI
     * thread. The thread it runs on may be interrupted. In this case, the macro
     * may report the interruption by an {@link InterruptedException}.
     * 
     * A {@link ProverTaskListener} can be provided to which the progress will
     * be reported. If no reports are desired, <code>null</code> can be used for
     * this parameter. If more than one listener is needed, consider combining
     * them using a single listener object using the composite pattern.
     * 
     * @param mediator
     *            the mediator (not <code>null</code>)
     * @param posInOcc
     *            the position in occurrence (may be <code>null</code>)
     * @param listener
     *            the listener to use for progress reports (may be
     *            <code>null</code>)
     * @throws InterruptedException
     *             if the application of the macro has been interrupted.
     */
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException;

    /**
     * Apply this macro on the given goals.
     *
     * This method can change the proof by applying rules to it.
     *
     * This method is usually called from a dedicated thread and not the GUI
     * thread. The thread it runs on may be interrupted. In this case, the macro
     * may report the interruption by an {@link InterruptedException}.
     *
     * A {@link ProverTaskListener} can be provided to which the progress will
     * be reported. If no reports are desired, <code>null</code> cna be used for
     * this parameter. If more than one listener is needed, consider combining
     * them using a single listener object using the composite pattern.
     *
     * @param mediator
     *            the mediator (not <code>null</code>)
     * @param goals
     *            the goals (not <code>null</code>)
     * @param posInOcc
     *            the position in occurrence (may be <code>null</code>)
     * @param listener
     *            the listener to use for progress reports (may be
     *            <code>null</code>)
     * @throws InterruptedException
     *             if the application of the macro has been interrupted.
     */
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException;

    /**
     * Apply this macro on the given node.
     *
     * This method can change the proof by applying rules to it.
     *
     * This method is usually called from a dedicated thread and not the GUI
     * thread. The thread it runs on may be interrupted. In this case, the macro
     * may report the interruption by an {@link InterruptedException}.
     *
     * A {@link ProverTaskListener} can be provided to which the progress will
     * be reported. If no reports are desired, <code>null</code> cna be used for
     * this parameter. If more than one listener is needed, consider combining
     * them using a single listener object using the composite pattern.
     *
     * @param mediator
     *            the mediator (not <code>null</code>)
     * @param node
     *            the node (not <code>null</code>)
     * @param posInOcc
     *            the position in occurrence (may be <code>null</code>)
     * @param listener
     *            the listener to use for progress reports (may be
     *            <code>null</code>)
     * @throws InterruptedException
     *             if the application of the macro has been interrupted.
     */
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          Node node,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException;

    /**
     * Gets the keyboard shortcut to invoke the macro (optional).
     * 
     * @return null if no shortcut or the key stroke to invoke the macro.
     */
    public javax.swing.KeyStroke getKeyStroke();

    /**
     * This observer acts as intermediate instance between the reports by the
     * strategy and the UI reporting progress.
     *
     * The number of total steps is computed and all local reports are
     * translated in termini of the total number of steps such that a continuous
     * progress is reported.
     *
     * fixes #1356
     */
    class ProgressBarListener extends ProofMacroListener {
        private int numberGoals;
        private int numberSteps;
        private int completedGoals;

        ProgressBarListener(ProofMacro macro, int numberGoals,
                            int numberSteps, ProverTaskListener l) {
            super(macro, l);
            this.numberGoals = numberGoals;
            this.numberSteps = numberSteps;
        }

        @Override
        public void taskStarted(String message, int size) {
            //assert size == numberSteps;
            String suffix = " [" + (completedGoals + 1) + "/" + numberGoals + "]";
            super.taskStarted(message + suffix, numberGoals * numberSteps);
            super.taskProgress(completedGoals * numberSteps);
        }

        @Override
        public void taskProgress(int position) {
            super.taskProgress(completedGoals * numberSteps + position);
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            super.taskFinished(info);
            completedGoals ++;
        }
    }
}