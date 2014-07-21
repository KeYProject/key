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

import static de.uka.ilkd.key.gui.Main.Verbosity.DEBUG;
import static de.uka.ilkd.key.gui.Main.Verbosity.HIGH;
import static de.uka.ilkd.key.gui.Main.Verbosity.NORMAL;
import static de.uka.ilkd.key.gui.Main.Verbosity.SILENT;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.ApplyTacletDialogModel;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.util.Debug;

public class ConsoleUserInterface extends AbstractUserInterface {
    private static final int PROGRESS_BAR_STEPS = 50;
    private static final String PROGRESS_MARK = ">";

    // Substitute for TaskTree (GUI) to facilitate side proofs in console mode
    private ImmutableList<Proof> proofStack = ImmutableSLList.<Proof>nil();

    private final BatchMode batchMode;
    private final byte verbosity;
    private KeYMediator mediator;

    // for a progress bar
    private int progressMax = 0;

   public ConsoleUserInterface(BatchMode batchMode, byte verbosity) {
    	this.batchMode = batchMode;
    	this.verbosity = verbosity;
        this.mediator  = new KeYMediator(this);
   }

   public ConsoleUserInterface(BatchMode batchMode, boolean verbose) {
       this(batchMode, verbose? DEBUG: NORMAL);
   }

   protected String getMacroConsoleOutput() {
       return "[ APPLY " + getMacro().getClass().getSimpleName() + " ]";
   }

   public void finish(Proof proof) {
       // setInteractive(false) has to be called because the ruleAppIndex
       // has to be notified that we work in auto mode (CS)
       mediator.setInteractive(false);
       startAndWaitForAutoMode(proof);
       if (verbosity >= HIGH) { // WARNING: Is never executed since application terminates via System.exit() before.
       	System.out.println(proof.statistics());
       }
   }

   public void taskFinished(TaskFinishedInfo info) {
       progressMax = 0; // reset progress bar marker
       final Proof proof = info.getProof();
       if (proof==null) {
           if (verbosity > SILENT) System.out.println("Proof loading failed");
           System.exit(1);
       }
       final int openGoals = proof.openGoals().size();
       final Object result2 = info.getResult();
       if (info.getSource() instanceof ApplyStrategy || info.getSource() instanceof ProofMacro) {
           if (verbosity >= HIGH) {
               System.out.println("]"); // end progress bar
           }
           if (verbosity > SILENT) {
               System.out.println("[ DONE  ... rule application ]");
               if (verbosity >= HIGH) {
                   System.out.println("\n== Proof "+ (openGoals > 0 ? "open": "closed")+ " ==");
                   final Proof.Statistics stat = info.getProof().statistics();
                   System.out.println("Proof steps: "+stat.nodes);
                   System.out.println("Branches: "+stat.branches);
                   System.out.println("Automode Time: "+stat.autoModeTime+"ms");
                   System.out.println("Time per step: "+stat.timePerStep+"ms");
               }
               System.out.println("Number of goals remaining open: " +
                       openGoals);
               System.out.flush();
           }
           batchMode.finishedBatchMode ( result2, info.getProof() );
           Debug.fail ( "Control flow should not reach this point." );
       } else if (info.getSource() instanceof ProblemLoader) {
           if (verbosity > SILENT) System.out.println("[ DONE ... loading ]");
           if (result2 != null) {
               if (verbosity > SILENT) System.out.println(result2);
               if (verbosity >= HIGH && result2 instanceof Throwable) {
                   ((Throwable) result2).printStackTrace();
               }
               System.exit(-1);
           }
           if(batchMode.isLoadOnly() ||  openGoals==0) {
               if (verbosity > SILENT)
                   System.out.println("Number of open goals after loading: " +
                           openGoals);
               System.exit(0);
           }
       }
   }

   @Override
    public void progressStarted(Object sender) {
        // TODO Implement ProblemInitializerListener.progressStarted
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.progressStarted(" + sender + ")");
        }
    }

    @Override
    public void progressStopped(Object sender) {
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.progressStopped(" + sender + ")");
        }
    }

    @Override
    public void proofCreated(ProblemInitializer sender,
            ProofAggregate proofAggregate) {
    }

    @Override
    public void reportException(Object sender, ProofOblInput input, Exception e) {
        // TODO Implement ProblemInitializerListener.reportException
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.reportException(" + sender + "," + input + "," + e + ")");
            e.printStackTrace();
        }
    }

    @Override
    public void reportStatus(Object sender, String status, int progress) {
        // TODO Implement ProblemInitializerListener.reportStatus
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.reportStatus(" + sender + "," + status + "," + progress + ")");
        }
    }

    @Override
    public void reportStatus(Object sender, String status) {
        // TODO Implement ProblemInitializerListener.reportStatus
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.reportStatus(" + sender + "," + status + ")");
        }
    }

    @Override
    public void resetStatus(Object sender) {
        // TODO Implement ProblemInitializerListener.resetStatus
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.resetStatus(" + sender + ")");
        }
    }

    @Override
    public void taskProgress(int position) {
        if (verbosity >= HIGH && progressMax > 0) {
            if ((position*PROGRESS_BAR_STEPS) % progressMax == 0) {
                System.out.print(PROGRESS_MARK);
            }
        }
    }

    @Override
    public void taskStarted(String message, int size) {
        progressMax = size;
        if (verbosity >= HIGH) {
            if (ApplyStrategy.PROCESSING_STRATEGY.equals(message)) {
                System.out.print(message+" ["); // start progress bar
            } else {
                System.out.println(message);
            }
        }
    }

    @Override
    public void setMaximum(int maximum) {
        // TODO Implement ProgressMonitor.setMaximum
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.setMaximum(" + maximum + ")");
        }
    }

    @Override
    public void setProgress(int progress) {
        // TODO Implement ProgressMonitor.setProgress
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.setProgress(" + progress + ")");
        }
    }

    @Override
    public void notify(NotificationEvent event) {
        if(verbosity >= DEBUG) {
        	System.out.println(event);
        }
    }

    @Override
    public void completeAndApplyTacletMatch(ApplyTacletDialogModel[] models, Goal goal) {
        if(verbosity >= DEBUG) {
        	System.out.println("Taclet match completion not supported by console.");
        }
    }

    @Override
    public boolean confirmTaskRemoval(String string) {
        return true;
    }

    @Override
    public void loadProblem(File file) {
		super.getProblemLoader(file, null, null, mediator).runSynchronously();
	}

   @Override
   public void loadProblem(File file, List<File> classPath, File bootClassPath) {
      super.getProblemLoader(file, classPath, bootClassPath, mediator).runSynchronously();
   }

   @Override
   public void openExamples() {
       System.out.println("Open Examples not suported by console UI.");
   }

   @Override
   public ProblemInitializer createProblemInitializer(Profile profile) {
      ProblemInitializer pi = new ProblemInitializer(this,
            new Services(profile, mediator.getExceptionHandler()),
            this);
      return pi;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYMediator getMediator() {
     return mediator;
   }

   /**
    * Checks if the verbose is active or not.
    * @return {@code true} verbose is active, {@code false} verbose is deactivated.
    */
   public boolean isVerbose() {
      return verbosity >= DEBUG;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isAutoModeSupported(Proof proof) {
      return true; // All proofs are supported.
   }

    /**
     * {@inheritDoc}
     */
    @Override
    public void removeProof(Proof proof) {
        if (proof != null) {
            if (!proofStack.isEmpty()) {
                Proof p = proofStack.head();
                proofStack = proofStack.removeAll(p);
                assert p.name().equals(proof.name());
                getMediator().setProof(proofStack.head());
            } else {
                // proofStack might be empty, though proof != null. This can
                // happen for symbolic execution tests, if proofCreated was not
                // called by the test setup.
            }
            proof.dispose();
        }
    }

   @Override
   public boolean selectProofObligation(InitConfig initConfig) {
      if(verbosity >= DEBUG) {
         System.out.println("Proof Obligation selection not supported by console.");
        }
      return false;
   }

   @Override
   public void proofRegistered(ProofEnvironmentEvent event) {
      mediator.setProof(event.getProofList().getFirstProof());
      proofStack = proofStack.prepend(event.getProofList().getFirstProof());
   }

}