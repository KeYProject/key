package de.uka.ilkd.key.ui;

import java.io.File;
import java.io.IOException;
import java.util.List;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.informationflow.macros.AbstractFinishAuxiliaryComputationMacro;
import de.uka.ilkd.key.informationflow.macros.StartAuxiliaryBlockComputationMacro;
import de.uka.ilkd.key.informationflow.macros.StartAuxiliaryLoopComputationMacro;
import de.uka.ilkd.key.informationflow.macros.StartAuxiliaryMethodComputationMacro;
import de.uka.ilkd.key.informationflow.po.InfFlowPO;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.macros.IFProofMacroConstants;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYResourceManager;
import de.uka.ilkd.key.util.MiscTools;

public abstract class AbstractMediatorUserInterface extends AbstractUserInterface implements RuleCompletionHandler {
   private final MediatorProofControl proofControl = createProofControl();
   
   @Override
   public MediatorProofControl getProofControl() {
      return proofControl;
   }

   protected MediatorProofControl createProofControl() {
      return new MediatorProofControl(this);
   }

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
}
