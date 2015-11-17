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

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo.TaskKind;

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

    /**
     * Gets the name of this macro.
     *
     * Used as menu entry
     *
     * @return a non-<code>null</code> constant string
     */
    public String getName();

    /**
     * Gets a unique short name for this macro that can be used in proof
     * scripts.
     *
     * If <code>null</code> is returned, the macro cannot be addressed from
     * within scripts.
     *
     * @return <code>null</code> if not supported, or a non-<code>null</code>
     *         constant string as the short name
     */
    public String getScriptCommandName();

    /**
     * Gets the category of this macro.
     *
     * Used as name of the menu under which the macro is sorted.
     * Return <code>null</code> if no submenu is to be created.
     *
     * @return a constant string, or <code>null</code>
     */
    public String getCategory();

    /**
     * Gets the description of this macro.
     *
     * Used as tooltip.
     *
     * @return a non-<code>null</code> constant string
     */
    public String getDescription();

    /**
     * Can this macro be applied on the given goals?
     *
     * This method should not make any changes but check if the macro can be
     * applied or not on the given goals.
     *
     * This method may be called from within the GUI thread and be compatible
     * with that fact.
     *
     * @param proof
     *            the current {@link Proof} (not <code>null</code>)
     * @param goals
     *            the goals (not <code>null</code>)
     * @param posInOcc
     *            the position in occurrence (may be <code>null</code>)
     *
     * @return <code>true</code>, if the macro is allowed to be applied
     */
    public boolean canApplyTo(Proof proof,
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
     * This method must be implemented to have the same effect as calling
     * {@link #canApplyTo(Proof, ImmutableList, PosInOccurrence)} with
     * <code>node.proof()</code> as proof and all open goals below
     * <code>node</code>.
     *
     * @param node
     *            the node (not <code>null</code>)
     * @param posInOcc
     *            the position in occurrence (may be <code>null</code>)
     *
     * @return <code>true</code>, if the macro is allowed to be applied
     */
    public boolean canApplyTo(Node node,
                              PosInOccurrence posInOcc);

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
     * @param uic
     *            the {@link UserInterfaceControl} to use
     * @param proof
     *            the current {@link Proof} (not <code>null</code>)
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
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          Proof proof,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException, Exception;

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
     * be reported. If no reports are desired, <code>null</code> can be used for
     * this parameter. If more than one listener is needed, consider combining
     * them using a single listener object using the composite pattern.
     *
     * @param uic
     *            the {@link UserInterfaceControl} to use
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
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          Node node,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException, Exception;

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
        private final int numberGoals;
        private final int numberSteps;
        private int completedGoals;

        ProgressBarListener(String name, int numberGoals,
                            int numberSteps, ProverTaskListener l) {
            super(name, l);
            this.numberGoals = numberGoals;
            this.numberSteps = numberSteps;
        }

        public ProgressBarListener(int size, int numberSteps,
                ProverTaskListener listener) {
            this("", size, numberSteps, listener);
        }

        @Override
        public void taskStarted(TaskStartedInfo info) {
            //assert size == numberSteps;
            String suffix = getMessageSuffix();
            super.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro,
                  info.getMessage() + suffix, numberGoals * numberSteps));
            super.taskProgress(completedGoals * numberSteps);
        }

        protected String getMessageSuffix() {
            return " [" + (completedGoals + 1) + "/" + numberGoals + "]";
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