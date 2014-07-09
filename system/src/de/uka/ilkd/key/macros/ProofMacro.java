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
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Proof.Statistics;

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

    ImmutableList<Goal> getGoals();

    /**
     * Used to determine whether {@link ProverTaskListener#taskFinished(TaskFinishedInfo)}
     * can be called after applying the macro. For the state being, this is only important
     * for invoking a macro from the command line. When creating a composite macro, which
     * consists of more than one macro applied after another, this method should be redefined
     * for all macros preceding the last macro application.
     * @return <code>true</code>, if the macro is not being directly followed by another macro
     */
    public boolean finishAfterMacro();

    void innerMacroFinished(TaskFinishedInfo info);

    ProofMacroListener getListener();

    static class CompositePTListener implements ProverTaskListener {
        private ProverTaskListener[] listeners;

        public CompositePTListener(ProverTaskListener[] l) {
            this.listeners = l;
        }

        public CompositePTListener(ProverTaskListener ptl1,
                                   ProverTaskListener ptl2) {
            this(new ProverTaskListener[]{ptl1, ptl2});
        }

        @Override
        public void taskStarted(String message, int size) {
            for (ProverTaskListener l: listeners) {
                if (l != null) {
                    l.taskStarted(message, size);
                }
            }
        }

        @Override
        public void taskProgress(int position) {
            for (ProverTaskListener l: listeners) {
                if (l != null) {
                    l.taskProgress(position);
                }
            }
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            for (ProverTaskListener l: listeners) {
                if (l != null) {
                    l.taskFinished(info);
                }
            }
        }
    }

    static class ProofMacroListener implements ProverTaskListener {
        ProofMacro macro;

        ProofMacroListener(ProofMacro macro) {
            this.macro = macro;
        }

        @Override
        public void taskStarted(String message, int size) {
            assert message != null;
        }

        @Override
        public void taskProgress(int position) {
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            macro.innerMacroFinished(info);
        }
    }

    static class ProofMacroFinishedInfo extends DefaultTaskFinishedInfo {

        ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals,
                               Proof proof, long time, int appliedRules,
                               int closedGoals) {
            super(macro, goals, proof, time, appliedRules, closedGoals);
        }

        ProofMacroFinishedInfo(ProofMacro macro, Goal goal, Proof proof,
                long time, int appliedRules, int closedGoals) {
            this(macro, ImmutableSLList.<Goal>nil().prepend(goal), proof,
                 time, appliedRules, closedGoals);
        }

        ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals,
                               Proof proof, Statistics statistics) {
            this(macro, goals, proof,
                 statistics == null ? 0 : statistics.time,
                 statistics == null ? 0 : statistics.totalRuleApps,
                 proof == null ? 0 : (proof.countBranches() - proof.openGoals().size()));
        }

        ProofMacroFinishedInfo(ProofMacro macro, Goal goal, Proof proof,
                               Statistics statistics) {
            this(macro, goal, proof,
                 statistics == null ? 0 : statistics.time,
                 statistics == null ? 0 : statistics.totalRuleApps,
                 proof == null ? 0 : (proof.countBranches() - proof.openGoals().size()));
        }

        ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals, Proof proof) {
            this(macro, goals, proof, proof == null ? null : proof.statistics());
        }

        ProofMacroFinishedInfo(ProofMacro macro, Goal goal, Proof proof) {
            this(macro, goal, proof, proof == null ? null : proof.statistics());
        }

        ProofMacroFinishedInfo(ProofMacro macro, Goal goal) {
            this(macro, goal, goal.proof());
        }

        ProofMacroFinishedInfo(ProofMacro macro, ImmutableList<Goal> goals) {
            this(macro, goals, goals.isEmpty() ? null : goals.head().proof());
        }

        ProofMacroFinishedInfo(ProofMacro macro, ProofMacroFinishedInfo info) {
            this(macro, info.getGoals(), info.getProof());
        }

        ProofMacro getMacro() {
            return (ProofMacro)getSource();
        }

        @SuppressWarnings("unchecked")
        ImmutableList<Goal> getGoals() {
            final Object result = getResult();
            if (result == null) {
                return ImmutableSLList.<Goal>nil();
            } else {
                return (ImmutableList<Goal>)result;
            }
        }
    }
}