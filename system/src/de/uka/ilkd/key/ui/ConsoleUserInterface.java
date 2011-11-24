package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.util.Debug;

public class ConsoleUserInterface implements UserInterface {

    private final MainWindow mainWindow;
    private final BatchMode batchMode;
    private final boolean verbose;

    public ConsoleUserInterface(MainWindow mainWindow, BatchMode batchMode, boolean verbose) {
        this.mainWindow = mainWindow;
        this.batchMode = batchMode;
        this.verbose = verbose;
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
            
            mainWindow.getMediator().startAutoMode();
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
        mainWindow.addProblem(proofAggregate);
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
    
}
