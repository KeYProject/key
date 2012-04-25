package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.key.util.KeYExceptionHandler;

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

public class WindowUserInterface implements UserInterface {

    private MainWindow mainWindow;
    
    public WindowUserInterface(MainWindow mainWindow) {
        this.mainWindow = mainWindow;
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
        mainWindow.addProblem(proofAggregate);
        mainWindow.setStandardStatusLine();
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
        final MainStatusLine sl = mainWindow.getStatusLine();
        if (info.getSource() instanceof ApplyStrategy) {
            sl.reset();            
            ApplyStrategy.ApplyStrategyInfo result = 
                    (ApplyStrategyInfo) info.getResult();

            Goal g = result.nonCloseableGoal();
            if(g == null) {               
                g = info.getProof().openGoals().head();
            } else {
                mainWindow.getMediator().goalChosen(g);
            }
            
            if (inStopAtFirstUncloseableGoalMode(info.getProof())) {
                // iff Stop on non-closeable Goal is selected a little
                // popup is generated and proof is stopped
                AutoDismissDialog dialog = new AutoDismissDialog(
                        "Couldn't close Goal Nr. "
                                + g.node().serialNr()
                                + " automatically");
                dialog.show();
            }
            mainWindow.displayResults(info.getTime(), 
                           info.getAppliedRules(), 
                           info.getClosedGoals(),
                           info.getProof().openGoals().size());                
        } else if (info.getSource() instanceof ProblemLoader) {
            if (!"".equals(info.getResult())) {
                final KeYExceptionHandler exceptionHandler = 
                    ((ProblemLoader)info.getSource()).getExceptionHandler();
                        ExceptionDialog.showDialog(mainWindow,     
                                exceptionHandler.getExceptions());
                        exceptionHandler.clear();
            } else {
                sl.reset();                    
                KeYMediator mediator = mainWindow.getMediator();
                mediator.getNotationInfo().refresh(mediator.getServices());
            }
        } else {
            sl.reset();
            if(info.toString() != ""){
                    mainWindow.displayResults(info.toString());
            }
        }
    }

    protected boolean inStopAtFirstUncloseableGoalMode(Proof proof) {
        return proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties().getProperty(
                        StrategyProperties.STOPMODE_OPTIONS_KEY)
                        .equals(StrategyProperties.STOPMODE_NONCLOSE);
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

}
