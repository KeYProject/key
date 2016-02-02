package de.uka.ilkd.key.ui;

import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;

import javax.swing.SwingWorker;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ProofMacroWorker;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * A {@link ProofControl} which performs the automode in a {@link SwingWorker}.
 * @author Martin Hentschel
 */
// TODO: This class should not know/use the AbstractMediatorUserInterfaceControl and the KeYMediator.
// Refactor the implementation and use events to update the user interface.
public class MediatorProofControl extends AbstractProofControl {
   private final AbstractMediatorUserInterfaceControl ui;

   public MediatorProofControl(AbstractMediatorUserInterfaceControl ui) {
      super(ui, ui);
      this.ui = ui;
   }

   private AutoModeWorker worker;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean selectedTaclet(Taclet taclet, Goal goal, PosInOccurrence pos) {
      boolean result = super.selectedTaclet(taclet, goal, pos);
      if (!result) {
         ui.notify(new GeneralFailureEvent("Taclet application failed." + taclet.name()));
      }
      return result;
   }
   
   @Override
   public void fireAutoModeStarted(ProofEvent e) {
      super.fireAutoModeStarted(e);
   }

   @Override
   public void fireAutoModeStopped(ProofEvent e) {
      super.fireAutoModeStopped(e);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void startAutoMode(Proof proof, ImmutableList<Goal> goals, ProverTaskListener ptl) {
      if (goals.isEmpty()) {
         ui.notify(new GeneralInformationEvent("No enabled goals available."));
         return;
     }
     worker = new AutoModeWorker(proof, goals, ptl);
     ui.getMediator().stopInterface(true);
     ui.getMediator().setInteractive(false);
     worker.execute();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stopAutoMode() {
      if (worker != null) {
         worker.cancel(true);
      }
      ui.getMediator().interrupt();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void waitWhileAutoMode() {
      while (ui.getMediator().isInAutoMode()) { // Wait until auto mode has stopped.
         try {
            Thread.sleep(100);
         }
         catch (InterruptedException e) {
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isInAutoMode() {
      return ui.getMediator().isInAutoMode();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isAutoModeSupported(Proof proof) {
      return super.isAutoModeSupported(proof) && 
             ui.getMediator().getSelectedProof() == proof;
   }


   /* <p>
    * Invoking start() on the SwingWorker causes a new Thread
    * to be created that will call construct(), and then
    * finished().  Note that finished() is called even if
    * the worker is interrupted because we catch the
    * InterruptedException in doWork().
    * </p>
    * <p>
    * <b>Attention:</b> Before this thread is started it is required to
    * freeze the MainWindow via
    * {@code
    * mediator().stopInterface(true);
    *   mediator().setInteractive(false);
    * }. The thread itself unfreezes the UI when it is finished.
    * </p>
    */
   private class AutoModeWorker extends SwingWorker<ApplyStrategyInfo, Object> {
       private final Proof proof;
       
       private final ImmutableList<Goal> goals;

       private final ApplyStrategy applyStrategy;
       
       public AutoModeWorker(final Proof proof,
                             final ImmutableList<Goal> goals,
                             ProverTaskListener ptl) {
           this.proof = proof;
           this.goals = goals;
           this.applyStrategy = new ApplyStrategy(proof.getInitConfig().getProfile().getSelectedGoalChooserBuilder().create());
           if (ptl != null) {
              applyStrategy.addProverTaskObserver(ptl);
           }
           applyStrategy.addProverTaskObserver(getDefaultProverTaskListener());

           if (ui.getMediator().getAutoSaver() != null) {
               applyStrategy.addProverTaskObserver(ui.getMediator().getAutoSaver());
           }
       }

       @Override
       protected void done() {
           try {
              ApplyStrategyInfo result = get();
           } catch (final InterruptedException exception) {
               notifyException(exception);
           } catch (final ExecutionException exception) {
               notifyException(exception);
           } catch (final CancellationException exception) {
               // when the user canceled it's not an error
           }
           finally {
              // make it possible to free memory and falsify the isAutoMode() property
              worker = null;
              // Clear strategy
              synchronized(applyStrategy) {// wait for apply Strategy to terminate
                  applyStrategy.removeProverTaskObserver(ui);
                  applyStrategy.clear();
              }
              ui.getMediator().setInteractive(true);
              ui.getMediator().startInterface(true);
           }
       }

       private void notifyException(final Exception exception) {
           ui.notify(new GeneralFailureEvent("An exception occurred during"
                   + " strategy execution.\n Exception:" + exception));
       }

       @Override
       protected ApplyStrategyInfo doInBackground() throws Exception {
           boolean stopMode = proof.getSettings().getStrategySettings()
                   .getActiveStrategyProperties().getProperty(
                           StrategyProperties.STOPMODE_OPTIONS_KEY)
                   .equals(StrategyProperties.STOPMODE_NONCLOSE);
           return applyStrategy.start(proof, goals, ui.getMediator().getMaxAutomaticSteps(),
                 ui.getMediator().getAutomaticApplicationTimeout(), stopMode);
       }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc) {
      KeYMediator mediator = ui.getMediator();
      final ProofMacroWorker worker = new ProofMacroWorker(node, macro, mediator, posInOcc);
      mediator.stopInterface(true);
      mediator.setInteractive(false);
      mediator.addInterruptedListener(worker);
      worker.execute();
   }
}
