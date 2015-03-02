package de.uka.ilkd.key.ui;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;

import javax.swing.SwingWorker;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.informationflow.macros.AbstractFinishAuxiliaryComputationMacro;
import de.uka.ilkd.key.informationflow.macros.StartAuxiliaryBlockComputationMacro;
import de.uka.ilkd.key.informationflow.macros.StartAuxiliaryLoopComputationMacro;
import de.uka.ilkd.key.informationflow.macros.StartAuxiliaryMethodComputationMacro;
import de.uka.ilkd.key.informationflow.po.InfFlowPO;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.IFProofMacroConstants;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYResourceManager;
import de.uka.ilkd.key.util.MiscTools;

public abstract class AbstractMediatorUserInterface extends AbstractUserInterface{
   /** 
    * called to open the build in examples 
    */
   public abstract void openExamples();
   
   /**
    * Returns the used {@link KeYMediator}.
    * @return The used {@link KeYMediator}.
    */
   public abstract KeYMediator getMediator();

   /**
    * loads the problem or proof from the given file
    * @param file the File with the problem description or the proof
    */
   public abstract void loadProblem(File file);

   private AutoModeWorker worker;

   protected ProblemLoader getProblemLoader(File file, List<File> classPath,
                                            File bootClassPath, KeYMediator mediator) {
       final ProblemLoader pl =
               new ProblemLoader(file, classPath, bootClassPath,
                                 AbstractProfile.getDefaultProfile(), false, mediator, true, null, this);
       return pl;
   }

   public boolean applyMacro() {
      assert macroChosen();
      final ProofMacro macro = getMacro();
      if (macro.canApplyTo(getMediator().getSelectedNode(), null)) {
          Debug.out("[ APPLY " + getMacro().getClass().getSimpleName() + " ]");
          Proof proof = getMediator().getSelectedProof();
          ProofMacroFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
          ProverTaskListener ptl = getListener();
          try {
              getMediator().stopInterface(true);
              getMediator().setInteractive(false);
              ptl.taskStarted(macro.getName(), 0);
              synchronized(macro) {
                  // wait for macro to terminate
                  info = macro.applyTo(getMediator().getSelectedNode(), null, ptl);
              }
          } catch(InterruptedException ex) {
              Debug.out("Proof macro has been interrupted:");
              Debug.out(ex);
          } finally {
              ptl.taskFinished(info);
              getMediator().setInteractive(true);
              getMediator().startInterface(true);
          }
          return true;
      } else {
          System.out.println(macro.getClass().getSimpleName() + " not applicable!");
      }
      return false;
  }
   
   @Override
   protected void macroFinished(ProofMacroFinishedInfo info) {
      super.macroFinished(info);
      
      /*
       * This solution is only a hack. TODO: Someone with deeper knowledge of the macros for information flow should
       * solve the whole issue by not at all registering side proofs in the GUI, but instead using the proof starter.
       * And maybe extend the proof starter by an option save after completion, so that the proofs get saved
       */
      if (info.getMacro() instanceof AbstractFinishAuxiliaryComputationMacro) {
    	 InfFlowProof initiatingProof = (InfFlowProof) info.getProof();
         Object sideProofObject = info.getValueFor(IFProofMacroConstants.SIDE_PROOF);
         if (sideProofObject instanceof InfFlowProof) { 
             final InfFlowProof sideProof = (InfFlowProof) sideProofObject;
             saveSideProof(sideProof);
             initiatingProof.addSideProof(sideProof);
             // make everyone listen to the proof remove
             getMediator().startInterface(true);
             getMediator().getUI().removeProof(sideProof);
             getMediator().getSelectionModel().setSelectedGoal(info.getGoals().head());
             // go into automode again
             getMediator().stopInterface(true);
         }
      } else if (info.getMacro() instanceof StartAuxiliaryBlockComputationMacro ||
              info.getMacro() instanceof StartAuxiliaryMethodComputationMacro ||
              info.getMacro() instanceof StartAuxiliaryLoopComputationMacro) {
          final InfFlowProof proof = (InfFlowProof) info.getProof();
          final Object poObject = info.getValueFor(IFProofMacroConstants.PO_FOR_NEW_SIDE_PROOF);

          if (poObject instanceof InfFlowPO) {
        	  InfFlowPO po = (InfFlowPO) poObject;
              final InfFlowProof p;
              synchronized (po) {
                  try {
                    p = (InfFlowProof) createProof(proof.getEnv().getInitConfigForEnvironment(), po);
                } catch (ProofInputException e) {
                    getMediator().notify(new ExceptionFailureEvent("PO generation for side proof failed.", e));
                    return;
                } 
              }
              p.unionIFSymbols(proof.getIFSymbols());
              // stop interface again, because it is activated by the proof
              // change through startProver; the ProofMacroWorker will activate
              // it again at the right time
              getMediator().stopInterface(true);
              getMediator().setInteractive(false);
          }
      }
   }

   /**
    * Try to save a side proof.
    * Saving does not rely on UI features, but failures are reported to the UI.
    * @param proof
    */
   private void saveSideProof(Proof proof) {
       String proofName = proof.name().toString();
       if (proofName.endsWith(".key")) {
           proofName = proofName.substring(0, proofName.lastIndexOf(".key"));
       } else if (proofName.endsWith(".proof")) {
           proofName = proofName.substring(0, proofName.lastIndexOf(".proof"));
       }
       final String filename = MiscTools.toValidFileName(proofName) + ".proof";
       final File toSave = new File(proof.getProofFile().getParentFile(), filename);
       final KeYResourceManager krm = KeYResourceManager.getManager();
       final ProofSaver ps = new ProofSaver(proof, toSave.getAbsolutePath(), krm.getSHA1());
       try {
           ps.save();
       } catch (IOException e) {
           reportException(this, null, e);
       }
   }

   @Override
   public ProofEnvironment createProofEnvironmentAndRegisterProof(ProofOblInput proofOblInput,
         ProofAggregate proofList, InitConfig initConfig) {
      final ProofEnvironment env = new ProofEnvironment(initConfig);
      env.addProofEnvironmentListener(this);
      env.registerProof(proofOblInput, proofList);
      return env;
   }

   /**
    * these methods are called immediately before automode is started to ensure that
    * the GUI can respond in a reasonable way, e.g., change the cursor to a waiting cursor
    */
   public void notifyAutoModeBeingStarted() {
   }

   /**
    * these methods are called when automode has been stopped to ensure that
    * the GUI can respond in a reasonable way, e.g., change the cursor to the default
    */
   public void notifyAutomodeStopped() {
   }

   public abstract void notify(NotificationEvent event);

   /**
    * asks if removal of a task is completed. This is useful to display a dialog to the user and asking her or
    * if on command line to allow it always.
    * @param message
    * @return true if removal has been granted
    */
   public boolean confirmTaskRemoval(String string) {
       return true;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean selectedTaclet(Taclet taclet, Goal goal, PosInOccurrence pos) {
      boolean result = super.selectedTaclet(taclet, goal, pos);
      if (!result) {
         notify(new GeneralFailureEvent("Taclet application failed." + taclet.name()));
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
   public void startAndWaitForAutoMode(Proof proof) {
      startAutoMode(proof);
      waitWhileAutoMode();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void startAutoMode(Proof proof, ImmutableList<Goal> goals, ProverTaskListener ptl) {
      if (goals.isEmpty()) {
         notify(new GeneralInformationEvent("No enabled goals available."));
         return;
     }
     worker = new AutoModeWorker(proof, goals, ptl);
     getMediator().stopInterface(true);
     getMediator().setInteractive(false);
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
      getMediator().interrupt();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void waitWhileAutoMode() {
      while (getMediator().isInAutoMode()) { // Wait until auto mode has stopped.
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
      return getMediator().isInAutoMode();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isAutoModeSupported(Proof proof) {
      return super.isAutoModeSupported(proof) && 
             getMediator().getSelectedProof() == proof;
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
           applyStrategy.addProverTaskObserver(getListener());

           if (getMediator().getAutoSaver() != null) {
               applyStrategy.addProverTaskObserver(getMediator().getAutoSaver());
           }
       }

       @Override
       protected void done() {
           try {
               get();
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
              applyStrategy.removeProverTaskObserver(AbstractMediatorUserInterface.this);
              applyStrategy.clear();
              // wait for apply Strategy to terminate
              getMediator().setInteractive(true);
              getMediator().startInterface(true);
           }
       }

       private void notifyException(final Exception exception) {
           AbstractMediatorUserInterface.this.notify(new GeneralFailureEvent("An exception occurred during"
                   + " strategy execution.\n Exception:" + exception));
       }

       @Override
       protected ApplyStrategyInfo doInBackground() throws Exception {
           boolean stopMode = proof.getSettings().getStrategySettings()
                   .getActiveStrategyProperties().getProperty(
                           StrategyProperties.STOPMODE_OPTIONS_KEY)
                   .equals(StrategyProperties.STOPMODE_NONCLOSE);
           return applyStrategy.start(proof, goals, getMediator().getMaxAutomaticSteps(),
                 getMediator().getAutomaticApplicationTimeout(), stopMode);
       }
   }
}
