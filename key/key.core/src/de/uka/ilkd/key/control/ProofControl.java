package de.uka.ilkd.key.control;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A {@link ProofControl} provides the user interface independent logic to apply rules on a proof.
 * This includes:
 * <ul>
 *    <li>Functionality to reduce the available rules ({@link #isMinimizeInteraction()} and {@link #setMinimizeInteraction(boolean)}).</li>
 *    <li>Functionality to list available rules.</li>
 *    <li>Functionality to apply a rule interactively.</li>
 *    <li>Functionality to apply rules by the auto mode synchronous or asynchronously in a different {@link Thread}.</li>
 *    <li>Functionality to execute a macro.</li>
 * </ul>
 * @author Martin Hentschel
 */
public interface ProofControl {
   public boolean isMinimizeInteraction();

   public void setMinimizeInteraction(boolean minimizeInteraction);

   /**
    * collects all applicable RewriteTaclets of the current goal (called by the
    * SequentViewer)
    *
    * @return a list of Taclets with all applicable RewriteTaclets
    */
   public ImmutableList<TacletApp> getRewriteTaclet(Goal focusedGoal, PosInOccurrence pos);

   /**
    * collects all applicable FindTaclets of the current goal (called by the
    * SequentViewer)
    *
    * @return a list of Taclets with all applicable FindTaclets
    */
   public ImmutableList<TacletApp> getFindTaclet(Goal focusedGoal, PosInOccurrence pos);

   /**
    * collects all applicable NoFindTaclets of the current goal (called by the
    * SequentViewer)
    *
    * @return a list of Taclets with all applicable NoFindTaclets
    */
   public ImmutableList<TacletApp> getNoFindTaclet(Goal focusedGoal);

   /**
    * collects all built-in rules that are applicable at the given sequent
    * position 'pos'.
    *
    * @param pos
    *           the PosInSequent where to look for applicable rules
    */
   public ImmutableList<BuiltInRule> getBuiltInRule(Goal focusedGoal, PosInOccurrence pos);
   
   public boolean selectedTaclet(Taclet taclet, Goal goal, PosInOccurrence pos);
   
   /**
    * Apply a RuleApp and continue with update simplification or strategy
    * application according to current settings.
    * @param app
    * @param goal
    */
   public void applyInteractive(RuleApp app, Goal goal);
   
   /** selected rule to apply
    * @param rule the selected built-in rule
    * @param pos the PosInSequent describes the position where to apply the
    * rule
    * @param forced a boolean indicating that if the rule is complete or can be made complete
    * automatically then the rule should be applied automatically without asking the user at all
    * (e.g. if a loop invariant is available do not ask the user to provide one)
    */
   public void selectedBuiltInRule(Goal goal, BuiltInRule rule, PosInOccurrence pos, boolean forced);
   
   /**
    * Returns the default {@link ProverTaskListener} which will be added to all started {@link ApplyStrategy} instances.
    * @return The default {@link ProverTaskListener} which will be added to all started {@link ApplyStrategy} instances.
    */
   public ProverTaskListener getDefaultProverTaskListener();
   
   public void addAutoModeListener(AutoModeListener p);

   public void removeAutoModeListener(AutoModeListener p);
   
   /**
    * Checks if the auto mode of this {@link UserInterfaceControl} supports the given {@link Proof}.
    * @param proof The {@link Proof} to check.
    * @return {@code true} auto mode support proofs, {@code false} auto mode don't support proof.
    */
   boolean isAutoModeSupported(Proof proof);

   /**
    * Checks if the auto mode is currently running.
    * @return {@code true} auto mode is running, {@code false} auto mode is not running.
    */
   boolean isInAutoMode();

   /**
    * Starts the auto mode for the given {@link Proof}.
    * @param proof The {@link Proof} to start auto mode of.
    */
   void startAutoMode(Proof proof);
   
   /**
    * Starts the auto mode for the given {@link Proof} and the given {@link Goal}s. 
    * @param proof The {@link Proof} to start auto mode of.
    * @param goals The {@link Goal}s to close.
    */
   void startAutoMode(Proof proof, ImmutableList<Goal> goals);
   
   /**
    * Requests to stop the current auto mode without blocking the current {@link Thread} until the auto mode has stopped.
    */
   void stopAutoMode();
   
   /**
    * Stops the currently running auto mode and blocks the current {@link Thread} until auto mode has stopped.
    */
   void stopAndWaitAutoMode();
   
   /**
    * Blocks the current {@link Thread} while the auto mode of this
    * {@link UserInterfaceControl} is active.
    */
   void waitWhileAutoMode();
   
   /**
    * Starts the auto mode for the given proof which must be contained
    * in this user interface and blocks the current thread until it
    * has finished.
    * @param proof The {@link Proof} to start auto mode and to wait for.
    * @param goals The {@link Goal}s to close.
    */
   void startAndWaitForAutoMode(Proof proof, ImmutableList<Goal> goals);
   
   /**
    * Starts the auto mode for the given proof which must be contained
    * in this user interface and blocks the current thread until it
    * has finished.
    * @param proof The {@link Proof} to start auto mode and to wait for.
    */
   void startAndWaitForAutoMode(Proof proof);
   
   public void startFocussedAutoMode(PosInOccurrence focus, Goal goal);
   
   /**
    * Runs the given {@link ProofMacro} at the given {@link PosInOccurrence} on the given {@link Node}.
    * @param node The {@link Node} to start macro at.
    * @param macro The {@link ProofMacro} to execute.
    * @param posInOcc The exact {@link PosInOccurrence} at which the {@link ProofMacro} is started at.
    */
   public void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc);
}
