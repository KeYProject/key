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

import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.KeyStroke;
import javax.swing.WindowConstants;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.joinrule.JoinRuleCompletion;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.ui.MediatorProofControl;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ThreadUtilities;

/**
 * Implementation of {@link UserInterfaceControl} which controls the {@link MainWindow}
 * with the typical user interface of KeY.
 * @author Mattias Ulbrich
 */
public class WindowUserInterfaceControl extends AbstractMediatorUserInterfaceControl {
    private final MainWindow mainWindow;

    private final LinkedList<InteractiveRuleApplicationCompletion> completions =
            new LinkedList<InteractiveRuleApplicationCompletion>();

    public WindowUserInterfaceControl(MainWindow mainWindow) {
        this.mainWindow = mainWindow;
        completions.add(new FunctionalOperationContractCompletion());
        completions.add(new DependencyContractCompletion());
        completions.add(new LoopInvariantRuleCompletion());
        completions.add(new BlockContractCompletion(mainWindow));
        completions.add(JoinRuleCompletion.INSTANCE);
    }

    @Override
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
    public void loadProblem(File file, 
                            List<File> classPath,
                            File bootClassPath,
                            List<File> includes) {
        mainWindow.addRecentFile(file.getAbsolutePath());
        getProblemLoader(file, classPath, bootClassPath, includes, getMediator()).runAsynchronously();
    }

    @Override
    public void loadProblem(File file) {
        loadProblem(file, null, null, null);
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
        super.taskFinished(info);
        if (info.getSource() instanceof ApplyStrategy) {
            if (!isAtLeastOneMacroRunning()) {
                resetStatus(this);
            }
            ApplyStrategy.ApplyStrategyInfo result =
                    (ApplyStrategyInfo) info.getResult();

            Proof proof = info.getProof();
            if (proof != null && !proof.closed() && mainWindow.getMediator().getSelectedProof() == proof) {
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
                if (proof != null && !proof.closed() && mainWindow.getMediator().getSelectedProof() == proof) {
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
                ProblemLoader problemLoader = (ProblemLoader) info.getSource();
                if(problemLoader.hasProofScript()) {
                    Pair<String, Location> scriptAndLoc;
                    try {
                        scriptAndLoc = problemLoader.readProofScript();
                        ProofScriptWorker psw = new ProofScriptWorker(mainWindow.getMediator(),
                                scriptAndLoc.first, scriptAndLoc.second);
                        psw.init();
                        psw.execute();
                    } catch (ProofInputException e) {
                        // TODO
                        e.printStackTrace();
                    }
                } else if (macroChosen()) {
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
        super.taskProgress(position);
        mainWindow.getStatusLine().setProgress(position);

    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        super.taskStarted(info);
        mainWindow.setStatusLine(info.getMessage(), info.getSize());
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
    public void completeAndApplyTacletMatch(TacletInstantiationModel[] models,
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
                                    List<File> includes,
                                    Properties poPropertiesToForce,
                                    boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
      if (file != null) {
         mainWindow.getRecentFiles().addRecentFile(file.getAbsolutePath());
      }
      try {
         getMediator().stopInterface(true);
         return super.load(profile, file, classPath, bootClassPath, includes, poPropertiesToForce, forceNewProfileOfNewProofs);
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
   public void proofDisposing(final ProofDisposedEvent e) {
      super.proofDisposing(e);
      // Remove proof from user interface
      ThreadUtilities.invokeAndWait(new Runnable() {
         @Override
         public void run() {
            mainWindow.getProofList().removeProof(e.getSource());            
         }
      });
    }

   @Override
   public boolean selectProofObligation(InitConfig initConfig) {
      return ProofManagementDialog.showInstance(initConfig);
   }

   @Override
   public void registerProofAggregate(ProofAggregate pa) {
      super.registerProofAggregate(pa);
      mainWindow.addProblem(pa);
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
             if ("".equals(result.getStatus())) {
                 this.resetStatus(this);
              } else {
                 this.reportStatus(this, result.getStatus());                         
              }
             getMediator().getSelectionModel().setSelectedNode(result.getNode());
             if (result.hasErrors()) {
                 throw new ProblemLoaderException(loader,
                       "Proof could only be loaded partially.\n" +
                             "In summary " + result.getErrorList().size() +
                             " not loadable rule application(s) have been detected.\n" +
                             "The first one:\n"+result.getErrorList().get(0).getMessage(), result.getErrorList().get(0));
             }
         } else {
            // should never happen as replay always returns a result object
             //TODO (DS): Why is it then there? If this happens, we will get\\
             // a NullPointerException just a line below...
            getMediator().getSelectionModel().setSelectedNode(loader.getProof().root());                         
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
    * @param includes Optional includes to consider.
    * @param makeMainWindowVisible Make KeY's {@link MainWindow} visible if it is not already visible?
    * @return The {@link KeYEnvironment} which contains all references to the loaded location.
    * @throws ProblemLoaderException Occurred Exception
    */
   public static KeYEnvironment<WindowUserInterfaceControl> loadInMainWindow(File location,
                                                                             List<File> classPaths,
                                                                             File bootClassPath,
                                                                             List<File> includes,
                                                                             boolean makeMainWindowVisible) throws ProblemLoaderException {
      return loadInMainWindow(null, location, classPaths, bootClassPath, includes, false, makeMainWindowVisible);
   }
   
   /**
    * Loads the given location and returns all required references as {@link KeYEnvironment}
    * with KeY's {@link MainWindow}.
    * @param profile The {@link Profile} to use.
    * @param location The location to load.
    * @param classPaths The class path entries to use.
    * @param bootClassPath The boot class path to use.
    * @param includes Optional includes to consider.
    * @param makeMainWindowVisible Make KeY's {@link MainWindow} visible if it is not already visible?
    * @param forceNewProfileOfNewProofs {@code} true {@link #profileOfNewProofs} will be used as {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file will be used for new proofs.
    * @return The {@link KeYEnvironment} which contains all references to the loaded location.
    * @throws ProblemLoaderException Occurred Exception
    */
   public static KeYEnvironment<WindowUserInterfaceControl> loadInMainWindow(Profile profile,
                                                                             File location,
                                                                             List<File> classPaths,
                                                                             File bootClassPath,
                                                                             List<File> includes,
                                                                             boolean forceNewProfileOfNewProofs,
                                                                             boolean makeMainWindowVisible) throws ProblemLoaderException {
      MainWindow main = MainWindow.getInstance();
      if (makeMainWindowVisible && !main.isVisible()) {
          main.setVisible(true);
      }
      AbstractProblemLoader loader = main.getUserInterface().load(profile, location, classPaths, bootClassPath, includes, null, forceNewProfileOfNewProofs);
      InitConfig initConfig = loader.getInitConfig();
      return new KeYEnvironment<WindowUserInterfaceControl>(main.getUserInterface(), initConfig, loader.getProof(), loader.getResult());
   }

   @Override
   public void notify(NotificationEvent event) {
      mainWindow.notify(event);
   }

   @Override
   public void reportWarnings(ImmutableSet<PositionedString> warnings) {
     final JDialog dialog = new JDialog(MainWindow.getInstance(), 
                                        SLEnvInput.getLanguage() + " warning", 
                                        true);
     dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
     Container pane = dialog.getContentPane();
     pane.setLayout(new BorderLayout());
     
     //top label
     JLabel label = new JLabel("The following non-fatal "
                               + "problems occurred when translating your " 
                               + SLEnvInput.getLanguage() + " specifications:");
     label.setBorder(BorderFactory.createEmptyBorder(5, 5, 0, 5));
     pane.add(label, BorderLayout.NORTH);
       
     //scrollable warning list
     JScrollPane scrollpane = new JScrollPane();
     scrollpane.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
     JList<PositionedString> list = new JList<PositionedString>(warnings.toArray(new PositionedString[warnings.size()]));
     list.setBorder(BorderFactory.createLoweredBevelBorder());
     scrollpane.setViewportView(list);
     pane.add(scrollpane, BorderLayout.CENTER);
 
     //ok button
     final JButton button = new JButton("OK");
     button.addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent e) {
             dialog.setVisible(false);
         }
     });
     Dimension buttonDim = new Dimension(100, 27);
     button.setPreferredSize(buttonDim);
     button.setMinimumSize(buttonDim);
     JPanel panel = new JPanel();
     panel.add(button);
     pane.add(panel, BorderLayout.SOUTH);
     dialog.getRootPane().setDefaultButton(button);
     
     button.registerKeyboardAction(
         new ActionListener() {
             @Override
            public void actionPerformed(ActionEvent event) {
                 if(event.getActionCommand().equals("ESC")) {
                     button.doClick();
                 }
             }
         },
         "ESC",
         KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
         JComponent.WHEN_IN_FOCUSED_WINDOW);
     
     dialog.setSize(700, 300);
     dialog.setLocationRelativeTo(MainWindow.getInstance());
     dialog.setVisible(true);
     dialog.dispose();
   }
}