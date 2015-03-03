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

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterface;
import de.uka.ilkd.key.ui.AbstractProofControl;
import de.uka.ilkd.key.ui.MediatorProofControl;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.MiscTools;
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

public class WindowUserInterface extends AbstractMediatorUserInterface {

    private final MainWindow mainWindow;

    private final LinkedList<InteractiveRuleApplicationCompletion> completions =
            new LinkedList<InteractiveRuleApplicationCompletion>();

    public WindowUserInterface(MainWindow mainWindow) {
        this.mainWindow = mainWindow;
        completions.add(new FunctionalOperationContractCompletion());
        completions.add(new DependencyContractCompletion());
        completions.add(new LoopInvariantRuleCompletion());
        completions.add(new BlockContractCompletion(mainWindow));
    }

    protected MediatorProofControl createProofControl() {
       return new MediatorProofControl(this) {
          /**
           * {@inheritDoc}
           */
          @Override
          public boolean isAutoModeSupported(Proof proof) {
             return super.isAutoModeSupported(proof) &&
                    mainWindow.getProofList().containsProof(proof);
          }          
       };
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
            if (!isAtLeastOneMacroRunning()) {
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
            if (!isAtLeastOneMacroRunning()) {
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
            return AbstractProofControl.completeBuiltInRuleAppByDefault(app, goal, forced);
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

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYMediator getMediator() {
      return mainWindow.getMediator();
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
      try {
         getMediator().stopInterface(true);
         return super.load(profile, file, classPath, bootClassPath, poPropertiesToForce, forceNewProfileOfNewProofs);
      }
      finally {
         getMediator().startInterface(true);
      }
   }

   /**
    * save proof in file. If autoSave is on, this will potentially overwrite already
    * existing proof files with the same name. Otherwise the save dialog pops up.
    * For loaded proofs both are turned off by default, i.e. only manual saving is
    * possible, and the save dialog never pops up automatically (except for hitting
    * the "Save ..." or "Save current proof" button).
    */
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

   protected static Pair<File, String> fileName(Proof proof, String fileExtension) {
       // TODO: why do we use GUI components here?
       final KeYFileChooser jFC = KeYFileChooser.getFileChooser("Choose filename to save proof");

       File selectedFile = null;
       if (proof != null) {
          selectedFile = proof.getProofFile();
       }
       // Suggest default file name if required
       final String defaultName;
       if (selectedFile == null) {
           defaultName = MiscTools.toValidFileName(proof.name().toString()) + fileExtension;
           selectedFile = new File(jFC.getCurrentDirectory(), defaultName);
       } else if (selectedFile.getName().endsWith(".proof") && fileExtension.equals(".proof")) {
           defaultName = selectedFile.getName();
       } else {
           String proofName = proof.name().toString();
           if (proofName.endsWith(".key")) {
               proofName = proofName.substring(0, proofName.lastIndexOf(".key"));
           } else if (proofName.endsWith(".proof")) {
               proofName = proofName.substring(0, proofName.lastIndexOf(".proof"));
           }
           defaultName = MiscTools.toValidFileName(proofName) + fileExtension;
           selectedFile = new File(selectedFile.getParentFile(), defaultName);
       }
       return new Pair<File, String>(selectedFile, defaultName);
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
   public void loadingStarted(AbstractProblemLoader loader) {
      getMediator().stopInterface(true);
      super.loadingStarted(loader);
   }

   @Override
   public void loadingFinished(AbstractProblemLoader loader, LoadedPOContainer poContainer, ProofAggregate proofList, ReplayResult result) throws ProblemLoaderException {
      super.loadingFinished(loader, poContainer, proofList, result);
      if (proofList != null) {
         getMediator().setProof(loader.getProof());
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
   
   
   

   
   /**
    * Loads the given location and returns all required references as {@link KeYEnvironment}
    * with KeY's {@link MainWindow}.
    * @param location The location to load.
    * @param classPaths The class path entries to use.
    * @param bootClassPath The boot class path to use.
    * @param makeMainWindowVisible Make KeY's {@link MainWindow} visible if it is not already visible?
    * @return The {@link KeYEnvironment} which contains all references to the loaded location.
    * @throws ProblemLoaderException Occurred Exception
    */
   public static KeYEnvironment<WindowUserInterface> loadInMainWindow(File location,
                                                                      List<File> classPaths,
                                                                      File bootClassPath,
                                                                      boolean makeMainWindowVisible) throws ProblemLoaderException {
      return loadInMainWindow(null, location, classPaths, bootClassPath, false, makeMainWindowVisible);
   }
   
   /**
    * Loads the given location and returns all required references as {@link KeYEnvironment}
    * with KeY's {@link MainWindow}.
    * @param profile The {@link Profile} to use.
    * @param location The location to load.
    * @param classPaths The class path entries to use.
    * @param bootClassPath The boot class path to use.
    * @param makeMainWindowVisible Make KeY's {@link MainWindow} visible if it is not already visible?
    * @param forceNewProfileOfNewProofs {@code} true {@link #profileOfNewProofs} will be used as {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file will be used for new proofs.
    * @return The {@link KeYEnvironment} which contains all references to the loaded location.
    * @throws ProblemLoaderException Occurred Exception
    */
   public static KeYEnvironment<WindowUserInterface> loadInMainWindow(Profile profile,
                                                                      File location,
                                                                      List<File> classPaths,
                                                                      File bootClassPath,
                                                                      boolean forceNewProfileOfNewProofs,
                                                                      boolean makeMainWindowVisible) throws ProblemLoaderException {
      MainWindow main = MainWindow.getInstance();
      if (makeMainWindowVisible && !main.isVisible()) {
          main.setVisible(true);
      }
      AbstractProblemLoader loader = main.getUserInterface().load(profile, location, classPaths, bootClassPath, null, forceNewProfileOfNewProofs);
      InitConfig initConfig = loader.getInitConfig();
      return new KeYEnvironment<WindowUserInterface>(main.getUserInterface(), initConfig, loader.getProof());
   }

   @Override
   public void notify(NotificationEvent event) {
      mainWindow.notify(event);
   }
}