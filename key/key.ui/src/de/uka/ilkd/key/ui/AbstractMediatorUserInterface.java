package de.uka.ilkd.key.ui;

import java.io.File;
import java.io.IOException;
import java.util.List;

import org.key_project.utils.collection.ImmutableList;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.macros.FinishAuxiliaryBlockComputationMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
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
      if (info.getMacro() instanceof FinishAuxiliaryBlockComputationMacro) { // TODO: Pass the other values via ProofMacroFinishedInfo (REFACTORING_FIX_ME)
         Proof initiatingProof = info.getProof();
         saveSideProof(proof);
         // make everyone listen to the proof remove
         getMediator().startInterface(true);
         initiatingProof.addSideProof(proof);
         getMediator().getUI().removeProof(proof);
         getMediator().getSelectionModel().setSelectedGoal(initiatingGoal);
         // go into automode again
         getMediator().stopInterface(true);
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
