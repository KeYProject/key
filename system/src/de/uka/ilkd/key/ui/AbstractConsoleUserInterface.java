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

import static de.uka.ilkd.key.core.Main.Verbosity.DEBUG;
import static de.uka.ilkd.key.core.Main.Verbosity.HIGH;
import static de.uka.ilkd.key.core.Main.Verbosity.NORMAL;

import java.io.File;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.TaskFinishedInfo;
import de.uka.ilkd.key.gui.ApplyTacletDialogModel;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * Common code of {@link ConsoleUserInterface} and {@link CustomUserInterface}.
 * Should generally be useful for any {@link UserInterface} implementation, that
 * is not GUI-dependent.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class AbstractConsoleUserInterface extends AbstractUserInterface {
    private static final int PROGRESS_BAR_STEPS = 50;
    private static final String PROGRESS_MARK = ">";
    int numOfInvokedMacros;


    // Substitute for TaskTree (GUI) to facilitate side proofs in console mode
    ImmutableList<Proof> proofStack = ImmutableSLList.<Proof>nil();

    final byte verbosity;
    KeYMediator mediator;

    // for a progress bar
    int progressMax = 0;

    public AbstractConsoleUserInterface(byte verbosity) {
        this.verbosity = verbosity;
        this.mediator  = new KeYMediator(this);
        this.numOfInvokedMacros = 0;
   }

   public AbstractConsoleUserInterface(boolean verbose) {
       this(verbose? DEBUG: NORMAL);
   }

   void finish(Proof proof) {
       // setInteractive(false) has to be called because the ruleAppIndex
       // has to be notified that we work in auto mode (CS)
       mediator.setInteractive(false);
       startAndWaitForAutoMode(proof);
       if (verbosity >= HIGH) { // WARNING: Is never executed since application terminates via System.exit() before.
           System.out.println(proof.statistics());
       }
   }

    @Override
    final protected void macroFinished(TaskFinishedInfo info) {
        numOfInvokedMacros--;
    }

    @Override
    final public void progressStarted(Object sender) {
        // TODO Implement ProblemInitializerListener.progressStarted
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.progressStarted(" + sender + ")");
        }
    }

    @Override
    final public void progressStopped(Object sender) {
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.progressStopped(" + sender + ")");
        }
    }

    /**
    * {@inheritDoc}
    */
   @Override
   final public void proofCreated(ProblemInitializer sender, ProofAggregate proofAggregate) {
      // Nothing to do
   }

    @Override
    final public void reportException(Object sender, ProofOblInput input, Exception e) {
        // TODO Implement ProblemInitializerListener.reportException
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.reportException(" + sender + "," + input + "," + e + ")");
            e.printStackTrace();
        }
    }

    @Override
    final public void reportStatus(Object sender, String status, int progress) {
        // TODO Implement ProblemInitializerListener.reportStatus
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.reportStatus(" + sender + "," + status + "," + progress + ")");
        }
    }

    @Override
    final public void reportStatus(Object sender, String status) {
        // TODO Implement ProblemInitializerListener.reportStatus
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.reportStatus(" + sender + "," + status + ")");
        }
    }

    @Override
    final public void resetStatus(Object sender) {
        // TODO Implement ProblemInitializerListener.resetStatus
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.resetStatus(" + sender + ")");
        }
    }

    @Override
    final public void taskProgress(int position) {
        if (verbosity >= HIGH && progressMax > 0) {
            if ((position*PROGRESS_BAR_STEPS) % progressMax == 0) {
                System.out.print(PROGRESS_MARK);
            }
        }
    }

    @Override
    final protected void macroStarted(String message,
                                int size) {
        numOfInvokedMacros++;
    }

    @Override
    final public void setMaximum(int maximum) {
        // TODO Implement ProgressMonitor.setMaximum
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.setMaximum(" + maximum + ")");
        }
    }

    @Override
    final public void setProgress(int progress) {
        // TODO Implement ProgressMonitor.setProgress
        if(verbosity >= DEBUG) {
            System.out.println("ConsoleUserInterface.setProgress(" + progress + ")");
        }
    }

    @Override
    final public void notify(NotificationEvent event) {
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
    final public boolean confirmTaskRemoval(String string) {
        return true;
    }

    @Override
    public void loadProblem(File file) {
        getProblemLoader(file, null, null, mediator).runSynchronously();
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
   final public KeYMediator getMediator() {
     return mediator;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   final public boolean isAutoModeSupported(Proof proof) {
      return true; // All proofs are supported.
   }

    /**
     * {@inheritDoc}
     */
    @Override
    final public void removeProof(Proof proof) {
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
    final public boolean selectProofObligation(InitConfig initConfig) {
        if(verbosity >= DEBUG) {
            System.out.println("Proof Obligation selection not supported by console.");
        }
        return false;
    }

}
