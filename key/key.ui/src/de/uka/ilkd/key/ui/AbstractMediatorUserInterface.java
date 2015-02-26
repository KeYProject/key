package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.List;

import org.key_project.utils.collection.ImmutableList;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.util.Debug;

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
          TaskFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
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
   public ProofEnvironment createProofEnvironmentAndRegisterProof(ProofOblInput proofOblInput,
         ProofAggregate proofList, InitConfig initConfig) {
      final ProofEnvironment env = new ProofEnvironment(initConfig);
      env.addProofEnvironmentListener(this);
      env.registerProof(proofOblInput, proofList);
      return env;
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
   public void startAutoMode(Proof proof) {
      KeYMediator mediator = getMediator();
      mediator.setProof(proof);
      mediator.startAutoMode();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void startAutoMode(Proof proof, ImmutableList<Goal> goals) {
      KeYMediator mediator = getMediator();
      mediator.setProof(proof);
      mediator.startAutoMode(goals);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stopAutoMode() {
      getMediator().stopAutoMode();
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
}
