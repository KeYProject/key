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

package de.uka.ilkd.key.ui;

import java.io.File;
import java.io.IOException;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.Pair;

/**
 * Implementation of {@link UserInterfaceControl} used by command line interface of KeY.
 */
public class ConsoleUserInterfaceControl extends AbstractMediatorUserInterfaceControl {
   private static final int PROGRESS_BAR_STEPS = 50;
   private static final String PROGRESS_MARK = ">";


   // Substitute for TaskTree (GUI) to facilitate side proofs in console mode
   ImmutableList<Proof> proofStack = ImmutableSLList.<Proof>nil();

   final byte verbosity;
   final KeYMediator mediator;

   // for a progress bar
   int progressMax = 0;

    
    // flag to indicate that a file should merely be loaded not proved. (for
    // "reload" testing)
    private final boolean loadOnly;
    
    
    /**
     * Current key problem file that is attempted to be proven.
     */
    private File keyProblemFile = null;
    
    /**
     * We want to record whether there was a proof that could not be proven.
     * {@link Main} calls System.exit() after all files have been loaded with
     * {@link #loadProblem(java.io.File)}. Program return value depends on
     * whether there has been a proof attempt that was not successful.
     */
    public boolean allProofsSuccessful = true;
    
    public ConsoleUserInterfaceControl(byte verbosity, boolean loadOnly) {
        this.verbosity = verbosity;
        this.mediator  = new KeYMediator(this);
        this.loadOnly = loadOnly;
    }

    public ConsoleUserInterfaceControl(boolean verbose, boolean loadOnly) {
        this(verbose? Verbosity.DEBUG: Verbosity.NORMAL, loadOnly);
    }

   private void printResults(final int openGoals,
                                  TaskFinishedInfo info,
                                  final Object result2) {
       if (verbosity >= Verbosity.HIGH) {
           System.out.println("]"); // end progress bar
       }
       if (verbosity > Verbosity.SILENT) {
           System.out.println("[ DONE  ... rule application ]");
           if (verbosity >= Verbosity.HIGH) {
               System.out.println("\n== Proof "+ (openGoals > 0 ? "open": "closed")+ " ==");
               final Statistics stat = info.getProof().getStatistics();
               System.out.println("Proof steps: "+stat.nodes);
               System.out.println("Branches: "+stat.branches);
               System.out.println("Automode Time: " + stat.autoModeTimeInMillis + "ms");
               System.out.println("Time per step: " + stat.timePerStepInMillis + "ms");
           }
           System.out.println("Number of goals remaining open: " + openGoals);
           System.out.flush();
       }
       // this seems to be a good place to free some memory
       Runtime.getRuntime().gc();

       /*
        * It is assumed that this part of the code is never reached, unless a 
        * value has been assigned to keyProblemFile in method loadProblem(File).
        */
       assert keyProblemFile != null : "Unexcpected null pointer. Trying to"
               + " save a proof but no corresponding key problem file is "
               + "available.";
       allProofsSuccessful &= saveProof(result2, info.getProof(), keyProblemFile);
       /*
        * We "delete" the value of keyProblemFile at this point by assigning
        * null to it. That way we prevent KeY from saving another proof (that
        * belongs to another key problem file) for a key problem file whose
        * execution cycle has already been finished (and whose proof has
        * already been saved). It is assumed that a new value has been assigned
        * beforehand in method loadProblem(File), if this part of the code is
        * reached again.
        */
       keyProblemFile = null;
   }

    @Override
   public void taskFinished(TaskFinishedInfo info) {
       super.taskFinished(info);
       progressMax = 0; // reset progress bar marker
       final Proof proof = info.getProof();
       if (proof==null) {
           if (verbosity > Verbosity.SILENT) {
               System.out.println("Proof loading failed");
               final Object error = info.getResult();
               if (error instanceof Throwable) {
                   ((Throwable) error).printStackTrace();
               }
           }
           System.exit(1);
       }
       final int openGoals = proof.openGoals().size();
       final Object result2 = info.getResult();
       if (info.getSource() instanceof ApplyStrategy ||
           info.getSource() instanceof ProofMacro) {
           if (!isAtLeastOneMacroRunning()) {
               printResults(openGoals, info, result2);
           }
       } else if (info.getSource() instanceof ProblemLoader) {
           if (verbosity > Verbosity.SILENT) System.out.println("[ DONE ... loading ]");
           if (result2 != null) {
               if (verbosity > Verbosity.SILENT) System.out.println(result2);
               if (verbosity >= Verbosity.HIGH && result2 instanceof Throwable) {
                   ((Throwable) result2).printStackTrace();
               }
               System.exit(-1);
           }
           if(loadOnly ||  openGoals==0) {
               if (verbosity > Verbosity.SILENT)
                   System.out.println("Number of open goals after loading: " +
                           openGoals);
               System.exit(0);
           }
           ProblemLoader problemLoader = (ProblemLoader) info.getSource();
           if(problemLoader.hasProofScript()) {
               try {
                   Pair<String, Location> script = problemLoader.readProofScript();
                   ProofScriptEngine pse = new ProofScriptEngine(script.first, script.second);
                   this.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, "Script started", 0));
                   pse.execute(this, proof);
                   // The start and end messages are fake to persuade the system ...
                   // All this here should refactored anyway ...
                   this.taskFinished(new ProofMacroFinishedInfo(new SkipMacro(), proof));
               } catch (Exception e) {
                   // TODO
                   e.printStackTrace();
                   System.exit(-1);
               }
           } else if (macroChosen()) {
               applyMacro();
           } else {
               finish(proof);
           }
       }
   }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        super.taskStarted(info);
        progressMax = info.getSize();
        if (verbosity >= Verbosity.HIGH) {
            if (TaskKind.Strategy.equals(info.getKind())) {
                System.out.print(info.getMessage()+" ["); // start progress bar
            } else {
                System.out.println(info.getMessage());
            }
        }
    }

    @Override
    public void loadProblem(File file) {
        /*
         * Current file is stored in a private field.
         * It will be used in method printResults() to determine file names,
         * in which proofs will be written.
         */
        keyProblemFile = file;
        getProblemLoader(file, null, null, null, mediator).runSynchronously();
    }

    @Override
    public void registerProofAggregate(ProofAggregate pa) {
        super.registerProofAggregate(pa);
        mediator.setProof(pa.getFirstProof());
        proofStack = proofStack.prepend(pa.getFirstProof());
    }
    
    private void finish(Proof proof) {
       // setInteractive(false) has to be called because the ruleAppIndex
       // has to be notified that we work in auto mode (CS)
       mediator.setInteractive(false);
       getProofControl().startAndWaitForAutoMode(proof);
       if (verbosity >= Verbosity.HIGH) { // WARNING: Is never executed since application terminates via System.exit() before.
           System.out.println(proof.getStatistics());
       }
   }

    @Override
    final public void progressStarted(Object sender) {
        // TODO Implement ProblemInitializerListener.progressStarted
        if(verbosity >= Verbosity.DEBUG) {
            System.out.println("ConsoleUserInterfaceControl.progressStarted(" + sender + ")");
        }
    }

    @Override
    final public void progressStopped(Object sender) {
        if(verbosity >= Verbosity.DEBUG) {
            System.out.println("ConsoleUserInterfaceControl.progressStopped(" + sender + ")");
        }
    }

    @Override
    final public void reportException(Object sender, ProofOblInput input, Exception e) {
        // TODO Implement ProblemInitializerListener.reportException
        if(verbosity >= Verbosity.DEBUG) {
            System.out.println("ConsoleUserInterfaceControl.reportException(" + sender + "," + input + "," + e + ")");
            e.printStackTrace();
        }
    }

    @Override
    final public void reportStatus(Object sender, String status, int progress) {
        // TODO Implement ProblemInitializerListener.reportStatus
        if(verbosity >= Verbosity.DEBUG) {
            System.out.println("ConsoleUserInterfaceControl.reportStatus(" + sender + "," + status + "," + progress + ")");
        }
    }

    @Override
    final public void reportStatus(Object sender, String status) {
        // TODO Implement ProblemInitializerListener.reportStatus
        if(verbosity >= Verbosity.DEBUG) {
            System.out.println("ConsoleUserInterfaceControl.reportStatus(" + sender + "," + status + ")");
        }
    }

    @Override
    final public void resetStatus(Object sender) {
        // TODO Implement ProblemInitializerListener.resetStatus
        if(verbosity >= Verbosity.DEBUG) {
            System.out.println("ConsoleUserInterfaceControl.resetStatus(" + sender + ")");
        }
    }

    @Override
    final public void taskProgress(int position) {
        super.taskProgress(position);
        if (verbosity >= Verbosity.HIGH && progressMax > 0) {
            if ((position*PROGRESS_BAR_STEPS) % progressMax == 0) {
                System.out.print(PROGRESS_MARK);
            }
        }
    }

    @Override
    final public void setMaximum(int maximum) {
        // TODO Implement ProgressMonitor.setMaximum
        if(verbosity >= Verbosity.DEBUG) {
            System.out.println("ConsoleUserInterfaceControl.setMaximum(" + maximum + ")");
        }
    }

    @Override
    final public void setProgress(int progress) {
        // TODO Implement ProgressMonitor.setProgress
        if(verbosity >= Verbosity.DEBUG) {
            System.out.println("ConsoleUserInterfaceControl.setProgress(" + progress + ")");
        }
    }

    @Override
    public void completeAndApplyTacletMatch(TacletInstantiationModel[] models, Goal goal) {
        if(verbosity >= Verbosity.DEBUG) {
         System.out.println("Taclet match completion not supported by console.");
        }
    }

   @Override
   final public void openExamples() {
       System.out.println("Open Examples not suported by console UI.");
   }

   @Override
   final public ProblemInitializer createProblemInitializer(Profile profile) {
      ProblemInitializer pi = new ProblemInitializer(this,
            new Services(profile),
            this);
      return pi;
   }

    /**
     * {@inheritDoc}
     */
    @Override
    public void proofDisposing(ProofDisposedEvent e) {
       super.proofDisposing(e);
       if (!proofStack.isEmpty()) {
          Proof p = proofStack.head();
          proofStack = proofStack.removeAll(p);
          assert p.name().equals(e.getSource().name());
          mediator.setProof(proofStack.head());
      } else {
          // proofStack might be empty, though proof != null. This can
          // happen for symbolic execution tests, if proofCreated was not
          // called by the test setup.
      }
    }

    @Override
    final public boolean selectProofObligation(InitConfig initConfig) {
        if(verbosity >= Verbosity.DEBUG) {
            System.out.println("Proof Obligation selection not supported by console.");
        }
        return false;
    }
    
   /**
    * {@inheritDoc}
    */
   @Override
   public KeYMediator getMediator() {
      return mediator;
   }

   @Override
   public void notify(NotificationEvent event) {
      if(verbosity >= Verbosity.DEBUG) {
         System.out.println(event);
      }
   }

   @Override
   public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
      return AbstractProofControl.completeBuiltInRuleAppByDefault(app, goal, forced);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void reportWarnings(ImmutableSet<PositionedString> warnings) {
      // Nothing to do
   }

   public static boolean saveProof(Object result, Proof proof,
         File keyProblemFile) {

      if (result instanceof Throwable) {
         throw new Error("Error in batchmode.", (Throwable) result);
      }

      // Save the proof before exit.

      String baseName = keyProblemFile.getAbsolutePath();
      int idx = baseName.indexOf(".key");
      if (idx == -1) {
         idx = baseName.indexOf(".proof");
      }
      baseName = baseName.substring(0, idx == -1 ? baseName.length() : idx);

      File f;
      int counter = 0;
      do {

         f = new File(baseName + ".auto." + counter + ".proof");
         counter++;
      }
      while (f.exists());

      try {
         // a copy with running number to compare different runs
         proof.saveToFile(new File(f.getAbsolutePath()));
         // save current proof under common name as well
         proof.saveToFile(new File(baseName + ".auto.proof"));
      }
      catch (IOException e) {
         e.printStackTrace();
      }

      if (proof.openGoals().size() == 0) {
         // Says that all Proofs have succeeded
         return true;
      }
      else {
         // Says that there is at least one open Proof
         return false;
      }
   }

}
