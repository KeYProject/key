package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.ApplyTacletDialogModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ProofStarter;

public class ConsoleUserInterface extends AbstractUserInterface {

    private final BatchMode batchMode;
    private final boolean verbose;
	private ProofStarter ps;
	private KeYMediator mediator;

    public ConsoleUserInterface(BatchMode batchMode, boolean verbose) {
    	this.batchMode = batchMode;
        this.verbose = verbose;
        this.mediator  = new KeYMediator(this);
    }

    public void taskFinished(TaskFinishedInfo info) {
        System.out.print("[ DONE ");
        if (info.getSource() instanceof ApplyStrategy) {
            System.out.println("  ... rule application ]");
            System.out.println("number of goals remaining open:" + 
                    info.getProof().openGoals().size());
            System.out.flush();
            batchMode.finishedBatchMode ( info.getResult(), 
                    info.getProof(), info.getTime(), 
                    info.getAppliedRules());
            Debug.fail ( "Control flow should not reach this point." );
        } else if (info.getSource() instanceof ProblemLoader) {
            System.out.println("  ... loading ]");
            if (!"".equals(info.getResult())) {
                System.out.println(info.getResult());
                    System.exit(-1);
            } 
            if(batchMode.isLoadOnly() ||  info.getProof().openGoals().size()==0) {
                System.out.println("number of open goals after loading:" + 
                        info.getProof().openGoals().size());              
                System.exit(0);
            }
            final Object result = ps.start();
            if (verbose) {
            	System.out.println(result);
            }
        }
    }

   @Override
    public void progressStarted(Object sender) {
        // TODO Implement ProblemInitializerListener.progressStarted
        if(verbose) {
            System.out.println("ConsoleUserInterface.progressStarted(" + sender + ")");
        }
    }

    @Override
    public void progressStopped(Object sender) {
        if(verbose) {
            System.out.println("ConsoleUserInterface.progressStopped(" + sender + ")");
        }
    }

    @Override
    public void proofCreated(ProblemInitializer sender,
            ProofAggregate proofAggregate) {
        // TODO Implement ProblemInitializerListener.proofCreated
        // XXX WHY AT THE MAINWINDOW?!?!
    	ps = new ProofStarter(this);
        ps.init(proofAggregate);
        mediator.setProof(proofAggregate.getFirstProof());
    }

    @Override
    public void reportException(Object sender, ProofOblInput input, Exception e) {
        // TODO Implement ProblemInitializerListener.reportException
        if(verbose) {
            System.out.println("ConsoleUserInterface.reportException(" + sender + "," + input + "," + e + ")");
            e.printStackTrace();
        }
    }

    @Override
    public void reportStatus(Object sender, String status, int progress) {
        // TODO Implement ProblemInitializerListener.reportStatus
        if(verbose) {
            System.out.println("ConsoleUserInterface.reportStatus(" + sender + "," + status + "," + progress + ")");
        }
    }

    @Override
    public void reportStatus(Object sender, String status) {
        // TODO Implement ProblemInitializerListener.reportStatus
        if(verbose) {
            System.out.println("ConsoleUserInterface.reportStatus(" + sender + "," + status + ")");
        }
    }

    @Override
    public void resetStatus(Object sender) {
        // TODO Implement ProblemInitializerListener.resetStatus
        if(verbose) {
            System.out.println("ConsoleUserInterface.resetStatus(" + sender + ")");
        }
    }

    @Override
    public void taskProgress(int position) {
        // TODO Implement ProverTaskListener.taskProgress
        if(verbose) {
            System.out.println("ConsoleUserInterface.taskProgress(" + position + ")");
        }
    }

    @Override
    public void taskStarted(String message, int size) {
        // TODO Implement ProverTaskListener.taskStarted
        if(verbose) {
            System.out.println("ConsoleUserInterface.taskStarted(" + message + "," + size + ")");
        }
    }

    @Override
    public void setMaximum(int maximum) {
        // TODO Implement ProgressMonitor.setMaximum
        if(verbose) {
            System.out.println("ConsoleUserInterface.setMaximum(" + maximum + ")");
        }
    }

    @Override
    public void setProgress(int progress) {
        // TODO Implement ProgressMonitor.setProgress
        if(verbose) {
            System.out.println("ConsoleUserInterface.setProgress(" + progress + ")");
        }
    }

    @Override
    public void notifyAutoModeBeingStarted() {
    	// nothing to do
    }

    @Override
    public void notifyAutomodeStopped() {
    	// nothing to do
    }

    @Override
    public void notify(NotificationEvent event) {
        if(verbose) {
        	System.out.println(event);
        }
    }

    @Override
    public void completeAndApplyTacletMatch(ApplyTacletDialogModel[] models, Goal goal) {
        if(verbose) {
        	System.out.println("Taclet match completion not supported by console.");
        }
    }

	@Override
    public boolean confirmTaskRemoval(String string) {
	    return true;
    }

	@Override
    public void loadProblem(File file) {
		super.loadProblem(file, null, null, mediator);
	}

   @Override
   public void loadProblem(File file, List<File> classPath, File bootClassPath) {
      super.loadProblem(file, classPath, bootClassPath, mediator);
   }

	@Override
    public void openExamples() {
		System.out.println("Open Examples not suported by console UI.");
    }

   @Override
   public ProblemInitializer createProblemInitializer() {
      ProblemInitializer pi = new ProblemInitializer(this, 
            mediator.getProfile(), 
            new Services(mediator.getExceptionHandler()), 
            true, 
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
      return verbose;
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
      // Nothing to do.
   }
}
