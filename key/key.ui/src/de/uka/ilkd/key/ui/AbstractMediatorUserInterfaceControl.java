package de.uka.ilkd.key.ui;

import java.io.File;
import java.io.IOException;
import java.util.List;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.RuleCompletionHandler;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.informationflow.macros.StartSideProofMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskStartedInfo;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentListener;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYResourceManager;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.ThreadUtilities;

/**
 * Provides a basic implementation of {@link UserInterfaceControl} for 
 * user interfaces in which a {@link KeYMediator} is available.
 * @author Martin Hentschel
 */
public abstract class AbstractMediatorUserInterfaceControl extends AbstractUserInterfaceControl implements RuleCompletionHandler, ProofEnvironmentListener, ProofDisposedListener {
   protected boolean saveOnly = false;

   private final MediatorProofControl proofControl = createProofControl();

   private ProofMacro autoMacro = new SkipMacro();
   
   @Override
   public MediatorProofControl getProofControl() {
      return proofControl;
   }

   protected MediatorProofControl createProofControl() {
      return new MediatorProofControl(this);
   }

   public void setSaveOnly(boolean s) {
       this.saveOnly = s;
   }
   
   public boolean isSaveOnly() {
       return this.saveOnly;
   }

   public void setMacro(ProofMacro macro) {
       assert macro != null;
       this.autoMacro = macro;
   }

   public ProofMacro getMacro() {
       return this.autoMacro;
   }

   public boolean macroChosen() {
       return !(getMacro() instanceof SkipMacro);
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
          ProverTaskListener ptl = this;
          try {
              getMediator().stopInterface(true);
              getMediator().setInteractive(false);
              ptl.taskStarted(new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Macro, macro.getName(), 0));
              synchronized(macro) {
                  // wait for macro to terminate
                  info = macro.applyTo(this, getMediator().getSelectedNode(), null, ptl);
              }
          } catch(InterruptedException ex) {
              Debug.out("Proof macro has been interrupted:");
              Debug.out(ex);
          } catch (Exception e) {
              Debug.out("Exception occurred during macro application:");
              Debug.out(e);
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
   protected void macroFinished(final ProofMacroFinishedInfo info) {
      super.macroFinished(info);
      if (info.getMacro() instanceof StartSideProofMacro) {
         final Proof initiatingProof = (Proof) info.getValueFor(StartSideProofMacro.PROOF_MACRO_FINISHED_INFO_KEY_ORIGINAL_PROOF);
         info.getProof().addProofDisposedListener(new ProofDisposedListener() {
            @Override
            public void proofDisposing(final ProofDisposedEvent e) {
               e.getSource().removeProofDisposedListener(this);
               macroSideProofDisposing(info, initiatingProof, e.getSource());
            }
            
            @Override
            public void proofDisposed(ProofDisposedEvent e) {
               // Nothing to do
            }
         });
         // stop interface again, because it is activated by the proof
         // change through startProver; the ProofMacroWorker will activate
         // it again at the right time
         ThreadUtilities.invokeAndWait(new Runnable() {
            @Override
            public void run() {
               getMediator().stopInterface(true);
               getMediator().setInteractive(false);
            }
         });
      }
   }
   
   protected void macroSideProofDisposing(final ProofMacroFinishedInfo initiatingInfo, final Proof initiatingProof, final Proof sideProof) {
      ThreadUtilities.invokeAndWait(new Runnable() {
         @Override
         public void run() {
            saveSideProof(sideProof);
            // make everyone listen to the proof remove
            getMediator().startInterface(true);
            if (initiatingProof.closed()) {
                getMediator().getSelectionModel().setSelectedNode(initiatingProof.root());
            } else {
                getMediator().getSelectionModel().setSelectedGoal(initiatingProof.openGoals().head());            
            }
            // go into automode again
            getMediator().stopInterface(true);
         }
      });
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
       final File proofFolder;
       if (proof.getProofFile() != null) {
          proofFolder = proof.getProofFile().getParentFile();
       } else { // happens when a Java file is loaded
          proofFolder = Main.getWorkingDir();
       }
       final File toSave = new File(proofFolder, filename);
       final KeYResourceManager krm = KeYResourceManager.getManager();
       final ProofSaver ps = new ProofSaver(proof, toSave.getAbsolutePath(), krm.getSHA1());
       try {
           ps.save();
       } catch (IOException e) {
           reportException(this, null, e);
       }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ProofEnvironment createProofEnvironmentAndRegisterProof(ProofOblInput proofOblInput, ProofAggregate proofList, InitConfig initConfig) {
      final ProofEnvironment env = new ProofEnvironment(initConfig);
      env.addProofEnvironmentListener(this);
      env.registerProof(proofOblInput, proofList);
      return env;
   }

   @Override
   public void proofUnregistered(ProofEnvironmentEvent event) {
      if (event.getSource().getProofs().isEmpty()) {
         event.getSource().removeProofEnvironmentListener(this);
      }
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
   public void proofDisposing(ProofDisposedEvent e) {
      e.getSource().removeProofDisposedListener(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void proofDisposed(ProofDisposedEvent e) {
      // Nothing to do
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void proofRegistered(ProofEnvironmentEvent event) {
      registerProofAggregate(event.getProofList());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void registerProofAggregate(ProofAggregate pa) {
      for (Proof proof : pa.getProofs()) {
         proof.addProofDisposedListener(this);
      }
   }
}
