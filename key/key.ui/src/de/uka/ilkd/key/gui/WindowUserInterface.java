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

package de.uka.ilkd.key.gui;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

import javax.swing.JOptionPane;

import org.key_project.utils.collection.ImmutableList;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.ui.AbstractUserInterface;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.Pair;

/**
 * This class is the starting point for the extraction of a unified
 * Userinterface for a GUI refactoring.
 *
 * It gathers all present interfaces and redirects action to the mainWindow.
 *
 * It is subject to change a lot at the moment.
 *
 * @author mattias ulbrich
 */

public class WindowUserInterface extends AbstractUserInterface {

    private final MainWindow mainWindow;
    private int numOfInvokedMacros;

    private final LinkedList<InteractiveRuleApplicationCompletion> completions =
            new LinkedList<InteractiveRuleApplicationCompletion>();

    public WindowUserInterface(MainWindow mainWindow) {
        this.mainWindow = mainWindow;
        completions.add(new FunctionalOperationContractCompletion());
        completions.add(new DependencyContractCompletion());
        completions.add(new LoopInvariantRuleCompletion());
        completions.add(new BlockContractCompletion(mainWindow));
        this.numOfInvokedMacros = 0;
    }

    /**
     * loads the problem or proof from the given file
     *
     * @param file the File with the problem description or the proof
     * @param classPath the class path entries to use.
     * @param bootClassPath the boot class path to use.
     */
    public void loadProblem(File file, List<File> classPath,
                            File bootClassPath) {
        mainWindow.addRecentFile(file.getAbsolutePath());
        getProblemLoader(file, classPath, bootClassPath, getMediator()).runAsynchronously();
    }

    @Override
    public void loadProblem(File file) {
        loadProblem(file, null, null);
    }

    @Override
    public void progressStarted(Object sender) {
        mainWindow.getMediator().stopInterface(true);
    }

    @Override
    public void progressStopped(Object sender) {
        mainWindow.getMediator().startInterface(true);
    }

    @Override
    public void proofCreated(ProblemInitializer sender,
                             ProofAggregate proofAggregate) {
    }

    @Override
    public void reportException(Object sender, ProofOblInput input, Exception e) {
        reportStatus(sender, input.name() + " failed");
    }

    @Override
    public void reportStatus(Object sender, String status, int progress) {
        mainWindow.setStatusLine(status, progress);
    }

    @Override
    public void reportStatus(Object sender, String status) {
        mainWindow.setStatusLine(status);
    }

    @Override
    public void resetStatus(Object sender) {
        mainWindow.setStandardStatusLine();
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        if (info.getSource() instanceof ApplyStrategy) {
            if (numOfInvokedMacros == 0) {
                resetStatus(this);
            }
            ApplyStrategy.ApplyStrategyInfo result =
                    (ApplyStrategyInfo) info.getResult();

            Proof proof = info.getProof();
            if (!proof.closed() && mainWindow.getMediator().getSelectedProof() == proof) {
                Goal g = result.nonCloseableGoal();
                if (g == null) {
                    g = proof.openGoals().head();
                }
                mainWindow.getMediator().goalChosen(g);
                if (inStopAtFirstUncloseableGoalMode(info.getProof())) {
                    // iff Stop on non-closeable Goal is selected a little
                    // popup is generated and proof is stopped
                    AutoDismissDialog dialog = new AutoDismissDialog(
                            "Couldn't close Goal Nr. " + g.node().serialNr()
                            + " automatically");
                    dialog.show();
                }
            }
            mainWindow.displayResults(info.toString());
        } else if (info.getSource() instanceof ProofMacro) {
            if (numOfInvokedMacros == 0) {
                resetStatus(this);
                assert info instanceof ProofMacroFinishedInfo;
                Proof proof = info.getProof();
                if (!proof.closed() && mainWindow.getMediator().getSelectedProof() == proof) {
                    Goal g = proof.openGoals().head();
                    mainWindow.getMediator().goalChosen(g);
                    if (inStopAtFirstUncloseableGoalMode(info.getProof())) {
                        // iff Stop on non-closeable Goal is selected a little
                        // popup is generated and proof is stopped
                        AutoDismissDialog dialog = new AutoDismissDialog(
                                "Couldn't close Goal Nr. " + g.node().serialNr()
                                + " automatically");
                        dialog.show();
                    }
                }
            }
        } else if (info.getSource() instanceof ProblemLoader) {
            resetStatus(this);
            Throwable result = (Throwable) info.getResult();
            if (info.getResult() != null) {
                ExceptionDialog.showDialog(mainWindow, result);
            } else if (getMediator().getUI().isSaveOnly()) {
                mainWindow.displayResults("Finished Saving!");
            } else {
                KeYMediator mediator = mainWindow.getMediator();
                mediator.getNotationInfo().refresh(mediator.getServices());
                if (macroChosen()) {
                    applyMacro();
                }
            }
        } else {
            resetStatus(this);
            if (!info.toString().isEmpty()) {
                mainWindow.displayResults(info.toString());
            }
        }
        // this seems to be a good place to free some memory
        Runtime.getRuntime().gc();
    }


    @Override
    protected void macroFinished(TaskFinishedInfo info) {
        numOfInvokedMacros--;
    }


    protected boolean inStopAtFirstUncloseableGoalMode(Proof proof) {
        return proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties().getProperty(
                        StrategyProperties.STOPMODE_OPTIONS_KEY).equals(
                                StrategyProperties.STOPMODE_NONCLOSE);
    }

    @Override
    public void taskProgress(int position) {
        mainWindow.getStatusLine().setProgress(position);

    }

    @Override
    public void taskStarted(String message, int size) {
        mainWindow.setStatusLine(message, size);
    }

    @Override
    protected void macroStarted(String message,
                                int size) {
        numOfInvokedMacros++;
    }

    @Override
    public void setMaximum(int maximum) {
        mainWindow.getStatusLine().setProgressBarMaximum(maximum);
    }

    @Override
    public void setProgress(int progress) {
        mainWindow.getStatusLine().setProgress(progress);
    }

    @Override
    public void notifyAutoModeBeingStarted() {
        mainWindow.setCursor(new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR));
        super.notifyAutoModeBeingStarted();
    }

    @Override
    public void notifyAutomodeStopped() {
        mainWindow.setCursor(new java.awt.Cursor(java.awt.Cursor.DEFAULT_CURSOR));
        super.notifyAutomodeStopped();
    }

    @Override
    public void completeAndApplyTacletMatch(ApplyTacletDialogModel[] models,
                                            Goal goal) {
        new TacletMatchCompletionDialog(mainWindow, models, goal, mainWindow.getMediator());
    }

    @Override
    public boolean confirmTaskRemoval(String string) {
        int answer = JOptionPane.showConfirmDialog(
                MainWindow.getInstance(), string, "Abandon Proof",
                JOptionPane.YES_NO_OPTION);
        return answer == JOptionPane.YES_OPTION;
    }

    @Override
    public void openExamples() {
        mainWindow.openExamples();
    }

    @Override
    public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
        if (mainWindow.getMediator().isInAutoMode()) {
            return super.completeBuiltInRuleApp(app, goal, forced);
        }
        IBuiltInRuleApp result = app;
        for (InteractiveRuleApplicationCompletion compl : completions ) {
            if (compl.canComplete(app)) {
                result = compl.complete(app, goal, forced);
                break;
            }
        }
        return (result != null && result.complete()) ? result : null;
    }

    @Override
    public ProblemInitializer createProblemInitializer(Profile profile) {
        ProblemInitializer pi = new ProblemInitializer(this,
                new Services(profile), this);
        return pi;
    }

   /**
    * Returns the used {@link KeYMediator}.
    * @return The used {@link KeYMediator}.
    */
   public KeYMediator getMediator() {
      return mainWindow.getMediator();
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

   
   /**
    * {@inheritDoc}
    */
   @Override
   public AbstractProblemLoader load(Profile profile,
                                    File file,
                                    List<File> classPath,
                                    File bootClassPath,
                                    Properties poPropertiesToForce,
                                    boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
      if (file != null) {
         mainWindow.getRecentFiles().addRecentFile(file.getAbsolutePath());
      } 
      
      AbstractProblemLoader loader = null;
      try {
         getMediator().stopInterface(true);
         loader = new SingleThreadProblemLoader(file, classPath, bootClassPath, profile, forceNewProfileOfNewProofs,
                                                this, false, poPropertiesToForce);
         loader.load();
         return loader;
      }
      catch(ProblemLoaderException e) {
          if (loader != null && loader.getProof() != null) {
              loader.getProof().dispose();
          }
          // rethrow that exception
          throw e;
      }
      catch (Throwable e) {
          if (loader != null && loader.getProof() != null) {
              loader.getProof().dispose();
          }
          throw new ProblemLoaderException(loader, e);
      }
      finally {
         getMediator().startInterface(true);
      }
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

   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isAutoModeSupported(Proof proof) {
      return mainWindow.getProofList().containsProof(proof);
   }

   @Override
   public File saveProof(Proof proof, String fileExtension) {
       final MainWindow mainWindow = MainWindow.getInstance();
       final KeYFileChooser jFC = KeYFileChooser.getFileChooser("Choose filename to save proof");

       Pair<File, String> f = fileName(proof, fileExtension);
       final boolean saved = jFC.showSaveDialog(mainWindow, f.first, f.second);
       File file = null;
       if (saved) {
           file = jFC.getSelectedFile();
           final String filename = file.getAbsolutePath();
           ProofSaver saver =
                   new ProofSaver(proof, filename, KeYConstants.INTERNAL_VERSION);
           String errorMsg;
           try {
               errorMsg = saver.save();
           } catch (IOException e) {
               errorMsg = e.toString();
           }
           if (errorMsg != null) {
               mainWindow.notify(new GeneralFailureEvent("Saving Proof failed.\n Error: " + errorMsg));
           } else {
              proof.setProofFile(file);
           }
       } else {
           jFC.resetPath();
       }
       return file;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeProof(Proof proof) {
       if (!proof.isDisposed()) {
          // The original code of this method. Neccessary?
           mainWindow.getProofList().removeProof(proof);


           // Run the garbage collector.
           Runtime r = Runtime.getRuntime();
           r.gc();
        }
    }

   @Override
   public boolean selectProofObligation(InitConfig initConfig) {
      return ProofManagementDialog.showInstance(initConfig);
   }

   @Override
   public void proofRegistered(ProofEnvironmentEvent event) {
      mainWindow.addProblem(event.getProofList());
      mainWindow.setStandardStatusLine();
   }

   @Override
   public void loadingStarted() {
      getMediator().stopInterface(true);
   }

   @Override
   public void loadingFinished(AbstractProblemLoader loader, LoadedPOContainer poContainer, ProofAggregate proofList, ReplayResult result) throws ProblemLoaderException {
      if (proofList != null) {
         // avoid double registration at specrepos as that is done already earlier in createProof
         // the UI method should just do the necessarily UI registrations
         this.createProofEnvironmentAndRegisterProof(poContainer.getProofOblInput(), proofList, loader.getInitConfig());
         getMediator().setProof(loader.getProof());
         getMediator().getSelectionModel().setSelectedProof(loader.getProof());                       
         if (result != null) {
            getMediator().getSelectionModel().setSelectedNode(result.getNode());
         } else {
            // should never happen as replay always returns a result object
            getMediator().getSelectionModel().setSelectedNode(loader.getProof().root());                         
         }

         if ("".equals(result.getStatus())) {
            this.resetStatus(this);
         } else {
            this.reportStatus(this, result.getStatus());                         
         }
         if (result.hasErrors()) {
            throw new ProblemLoaderException(loader,
                  "Proof could only be loaded partially.\n" +
                        "In summary " + result.getErrorList().size() +
                        " not loadable rule application(s) have been detected.\n" +
                        "The first one:\n"+result.getErrorList().get(0).getMessage(), result.getErrorList().get(0));
         }
      }
        getMediator().resetNrGoalsClosedByHeuristics();
        if (poContainer != null && poContainer.getProofOblInput() instanceof KeYUserProblemFile) {
            ((KeYUserProblemFile)poContainer.getProofOblInput()).close();
        }
   }
}