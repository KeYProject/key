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

package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.io.*;
import java.util.*;

import javax.swing.JOptionPane;
import javax.swing.JProgressBar;
import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.smt.InformationWindow.Information;
import de.uka.ilkd.key.gui.smt.ProgressDialog.Modus;
import de.uka.ilkd.key.gui.smt.ProgressDialog.ProgressDialogListener;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;
import de.uka.ilkd.key.smt.SMTSolver.SolverState;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;

public class SolverListener implements SolverLauncherListener {
        private ProgressDialog progressDialog;
       private ProgressModel progressModel ;
        // Every intern SMT problem refers to one solver
        private Collection<InternSMTProblem> problems = new LinkedList<InternSMTProblem>();
        // Every SMT problem refers to many solvers.
        private Collection<SMTProblem> smtProblems = new LinkedList<SMTProblem>();
        private boolean [][] problemProcessed;
        private int         finishedCounter;
        private Timer timer = new Timer();
        private final SMTSettings settings;
        private final static Color RED = new Color(180, 43, 43);
        private final static Color GREEN = new Color(43, 180, 43);
        private static int FILE_ID = 0;

        private static final int RESOLUTION = 1000;

        private class InternSMTProblem {
                final int problemIndex;
                final int solverIndex;
                final SMTSolver solver;
                final SMTProblem problem;
                final LinkedList<Information> information = new LinkedList<Information>();

                public InternSMTProblem(int problemIndex, int solverIndex,
                                SMTProblem problem, SMTSolver solver) {
                        super();
                        this.problemIndex = problemIndex;
                        this.solverIndex = solverIndex;
                        this.problem = problem;
                        this.solver = solver;
                }

                public int getSolverIndex() {
                        return solverIndex;
                }

                public int getProblemIndex() {
                        return problemIndex;
                }

                public SMTProblem getProblem() {
                        return problem;
                }
                
                private void addInformation(String title, String content){
                        information.add(new Information(title, content, solver.name()));
                }
                
                public boolean createInformation(){
                        if (solver.getException() != null) {

                                StringWriter writer = new StringWriter();

                                solver.getException().printStackTrace(
                                                new PrintWriter(writer));
                                addInformation("Error-Message",solver.getException()
                                                .toString()
                                                + "\n\n"
                                                + writer
                                                                .toString());     
                                

                        }
                        addInformation("Translation", solver.getTranslation());
                        if (solver.getTacletTranslation() != null) {
                                addInformation("Taclets", solver
                                                .getTacletTranslation()
                                                .toString());
                        }
                        addInformation("Solver Output",
                                        solver.getSolverOutput());

                        Collection<Throwable> exceptionsOfTacletTranslation = solver
                                        .getExceptionsOfTacletTranslation();
                        if (!exceptionsOfTacletTranslation.isEmpty()) {
                                String exceptionText = "The following exceptions have ocurred while translating the taclets:\n\n";
                                int i = 1;
                                for (Throwable e : exceptionsOfTacletTranslation) {
                                        exceptionText += i + ". "
                                                        + e.getMessage();
                                        StringWriter sw = new StringWriter();
                                        PrintWriter pw = new PrintWriter(sw);
                                        e.printStackTrace(pw);
                                        exceptionText += "\n\n" + sw.toString();
                                        exceptionText += "\n #######################\n\n";
                                        i++;
                                }
                                addInformation("Warning", exceptionText);
                        }
                        return solver.getException() != null;
                }
                
                @Override
                public String toString() {
                        return solver.name() +" applied on "+problem.getName();
                }

        }
        

        public SolverListener(SMTSettings settings) {
                this.settings = settings;
        }

        @Override
        public void launcherStopped(SolverLauncher launcher,
                        Collection<SMTSolver> problemSolvers) {
                timer.cancel();
                
  
                storeInformation();
                List<InternSMTProblem> problemsWithException = new LinkedList<InternSMTProblem>();
                progressModel.setEditable(true);
                refreshDialog();
                progressDialog.setModus(Modus.discardModus);
                for (InternSMTProblem problem : problems) {
                        if(problem.createInformation()){
                                problemsWithException.add(problem);
                        }

                }
                if (!problemsWithException.isEmpty()) {
                	 for(InternSMTProblem problem : problemsWithException){
                		progressDialog.addInformation("Exception for "+problem.toString()+".", Color.RED,problem);
                	 }
                } else {
                        if (settings.getModeOfProgressDialog() == ProofIndependentSMTSettings.PROGRESS_MODE_CLOSE) {
                                applyEvent(launcher);
                        }
                }
        }

        private String getTitle(SMTProblem p) {
                String title = "";
                Iterator<SMTSolver> it = p.getSolvers().iterator();
                while (it.hasNext()) {
                        title += it.next().name();
                        if (it.hasNext()) {
                                title += ", ";
                        }
                }
                return title;
        }

        private void applyResults() {
                for (SMTProblem problem : smtProblems) {
                        if (problem.getFinalResult().isValid() == ThreeValuedTruth.VALID) {
                        	IBuiltInRuleApp app = 
                        			RuleAppSMT.rule.createApp( null ).
                        					     setTitle( getTitle(problem) );
                        	problem.getGoal().apply(app);
                        }
                }

        }
        
        private void showInformation(InternSMTProblem problem){	
        	    new InformationWindow(problem.solver,problem.information,"Information for "+ problem.toString());
        }

        private void prepareDialog(Collection<SMTProblem> smtproblems,
                        Collection<SolverType> solverTypes,
                        final SolverLauncher launcher) {
                this.smtProblems = smtproblems;
                progressModel = new ProgressModel();

                String[] captions = new String[smtProblems.size()];
               
                int i = 0;
                for (SMTProblem problem : smtproblems) {
                        captions[i] = problem.getName();
                        i++;
                }

                progressModel.addColumn(new ProgressModel.TitleColumn(captions));
                String[] titles = new String[solverTypes.size() + 1];
                problemProcessed = new boolean[solverTypes.size()][smtProblems.size()];
                titles[0] = "";
                i = 1;
                for (SolverType type : solverTypes) {
                        progressModel.addColumn(new ProgressModel.ProcessColumn(
                                        smtproblems.size()));
                        titles[i] = type.getName();
                        i++;
                }

                
                String names[] = new String[smtproblems.size()]; //never read
                int x = 0,y=0;
                for (SMTProblem problem : smtproblems) {
                        y = 0;
                        for (SMTSolver solver : problem.getSolvers()) {
                                this.problems.add(new InternSMTProblem(x, y,
                                                problem, solver));
                                y++;
                        }
                        names[x] = problem.getName();
                        x++;
                }
       
                
                boolean ce = solverTypes.contains(SolverType.Z3_CE_SOLVER);
                
                    

                progressDialog = new ProgressDialog(
                                progressModel,new ProgressDialogListenerImpl(launcher, ce),ce,RESOLUTION,smtproblems.size()*solverTypes.size(), new String[] {}, titles);

                for(SolverType type : solverTypes){
                	if(type.supportHasBeenChecked() && !type.isSupportedVersion()){
                		addWarning(type);
                	}
                }
         
                SwingUtilities.invokeLater(new Runnable() {

                        @Override
                        public void run() {
                                progressDialog.setVisible(true);
                        }
                });

        }
        
       

		private InternSMTProblem getProblem(int col,int row){
                for(InternSMTProblem problem : problems){
                        if(problem.problemIndex == row && problem.solverIndex == col){
                                return problem;
                        }
                }
                return null;
        }

        private void stopEvent(final SolverLauncher launcher) {
                launcher.stop();
        }

        private void discardEvent(final SolverLauncher launcher) {
                launcher.stop();
                progressDialog.setVisible(false);
        }

        private void applyEvent(final SolverLauncher launcher) {
                launcher.stop();
                applyResults();
                progressDialog.setVisible(false);
        }

        @Override
        public void launcherStarted(final Collection<SMTProblem> smtproblems,
                        final Collection<SolverType> solverTypes,
                        final SolverLauncher launcher) {
                prepareDialog(smtproblems, solverTypes, launcher);
               
                setProgressText(0);
                timer.schedule(new TimerTask() {
                        @Override
                        public void run() {
                                refreshDialog();
                        }
                }, 0, 10);
        }

        private void refreshDialog() {
                for (InternSMTProblem problem : problems) {
                        refreshProgessOfProblem(problem);
                }
        }

        private long calculateProgress(InternSMTProblem problem) {
                long maxTime = problem.solver.getTimeout();
                long startTime = problem.solver.getStartTime();
                long currentTime = System.currentTimeMillis();

                return RESOLUTION - ((startTime - currentTime) * RESOLUTION)
                                / maxTime;
        }

        private float calculateRemainingTime(InternSMTProblem problem) {
                long startTime = problem.solver.getStartTime();
                long currentTime = System.currentTimeMillis();
                long temp = (startTime - currentTime) / 100;
                return Math.max((float) temp / 10.0f, 0);
        }

 

        private boolean refreshProgessOfProblem(InternSMTProblem problem) {
                SolverState state = problem.solver.getState();
                switch (state) {
                case Running:
                        running(problem);
                        return true;
                case Stopped:
                        stopped(problem);
                        return false;
                case Waiting:
                        waiting(problem);
                        return true;

                }
                return true;

        }

        private void waiting(InternSMTProblem problem) {

        }

        private void running(InternSMTProblem problem) {
                long progress = calculateProgress(problem);
                progressModel.setProgress((int)progress, problem.getSolverIndex(),problem.getProblemIndex());
                float remainingTime = calculateRemainingTime(problem);
                progressModel.setText(Float.toString(remainingTime) + " sec.", problem.getSolverIndex(),problem.getProblemIndex());
        }
        
        private void setProgressText(int value){
                JProgressBar bar = progressDialog.getProgressBar();
                if(bar.getMaximum() == 1){
                        bar.setString(value == 0 ? "Processing...": "Finished.");
                        bar.setStringPainted(true); 
                }else{
                        bar.setString("Processed " + value + " of " + bar.getMaximum() + " problems.");
                        bar.setStringPainted(true);
                }
                        
        }

        private void stopped(InternSMTProblem problem) {
                int x = problem.getSolverIndex();
                int y = problem.getProblemIndex();
                
                if(!problemProcessed[x][y]){
                        finishedCounter++;
                        progressDialog.setProgress(finishedCounter);
                        JProgressBar bar = progressDialog.getProgressBar();
                        bar.setValue(finishedCounter);
                        setProgressText(finishedCounter);
                        problemProcessed[x][y] = true;
                }
    
                if (problem.solver.wasInterrupted()) {
                        interrupted(problem);
                } else if (problem.solver.getFinalResult().isValid() == ThreeValuedTruth.VALID) {
        
                        successfullyStopped(problem,x,y);
                } else if (problem.solver.getFinalResult().isValid() == ThreeValuedTruth.FALSIFIABLE) {
   
                        unsuccessfullyStopped(problem,x,y);
                } else {
                 
                        unknownStopped(problem,x,y);
                }
           
        }

        private void interrupted(InternSMTProblem problem) {
                ReasonOfInterruption reason = problem.solver
                                .getReasonOfInterruption();
                int x = problem.getSolverIndex();
                int y = problem.getProblemIndex();
                switch (reason) {
                case Exception:
                        progressModel.setProgress(0,x,y);
                        progressModel.setTextColor(RED,x,y);
                        progressModel.setText("Exception!",x,y);
               
            

                        break;
                case NoInterruption:
                        throw new RuntimeException(
                                        "This position should not be reachable!");

                case Timeout:
                        progressModel.setProgress(0, x,y);                        
                        progressModel.setText("Timeout.",x,y);
        
                        break;
                case User:
                        progressModel.setText("Interrupted by user.",x,y);
                        break;
                }
        }

        private void successfullyStopped(InternSMTProblem problem, int x, int y) {
                
        		
        	
                progressModel.setProgress(0,x,y);
                progressModel.setTextColor(GREEN,x,y);
                if(problem.solver.getType()==SolverType.Z3_CE_SOLVER){
                	progressModel.setText("No Counterexample.",x,y);           
        		}
                else{
                	progressModel.setText("Valid.",x,y);
                }
                
               
        }

        private void unsuccessfullyStopped(InternSMTProblem problem, int x, int y) {
                progressModel.setProgress(0,x,y);
                progressModel.setTextColor(RED,x,y);
                progressModel.setText("Counter Example.",x,y);

        }

        private void unknownStopped(InternSMTProblem problem, int x, int y) {
                progressModel.setProgress(0,x,y);
                progressModel.setTextColor(Color.BLUE,x,y);
                progressModel.setText("Unknown.",x,y);
        }

        private void storeInformation() {

                if (settings.storeSMTTranslationToFile()
                                || (settings.makesUseOfTaclets() && settings
                                                .storeTacletTranslationToFile())) {
                        for (InternSMTProblem problem : problems) {
                                storeInformation(problem.getProblem());
                        }
                }

        }

        private void storeInformation(SMTProblem problem) {
                for (SMTSolver solver : problem.getSolvers()) {
                        if (settings.storeSMTTranslationToFile()) {
                                storeSMTTranslation(solver, problem.getGoal(),
                                                solver.getTranslation());
                        }
                        if (settings.makesUseOfTaclets()
                                        && settings
                                                        .storeTacletTranslationToFile()
                                        && solver.getTacletTranslation() != null) {
                                storeTacletTranslation(solver, problem
                                                .getGoal(), solver
                                                .getTacletTranslation());
                        }
                }
        }

        private void storeTacletTranslation(SMTSolver solver, Goal goal,
                        TacletSetTranslation translation) {
                String path = settings.getPathForTacletTranslation();
                path = finalizePath(path, solver, goal);
                storeToFile(translation.toString(), path);
        }

        private void storeSMTTranslation(SMTSolver solver, Goal goal,
                        String problemString) {
                String path = settings.getPathForSMTTranslation();
                
                String fileName = goal.proof().name()+"_"+goal.getTime()+"_"+solver.name()+".smt";
                path = path+File.separator+fileName;              
                path = finalizePath(path, solver, goal);
                storeToFile(problemString, path);

        }

        private void storeToFile(String text, String path) {
                try {
                        final BufferedWriter out2 = new BufferedWriter(
                                        new FileWriter(path));
                        out2.write(text);
                        out2.close();
                } catch (IOException e) {
                        throw new RuntimeException("Could not store to file "
                                        + path + ".", e);
                }
        }

        private String finalizePath(String path, SMTSolver solver, Goal goal) {
                Calendar c = Calendar.getInstance();
                String date = c.get(Calendar.YEAR) + "-"
                                + c.get(Calendar.MONTH) + "-"
                                + c.get(Calendar.DATE);
                String time = c.get(Calendar.HOUR_OF_DAY) + "-"
                                + c.get(Calendar.MINUTE) + "-"
                                + c.get(Calendar.SECOND);

                path = path.replaceAll("%d", date);
                path = path.replaceAll("%s", solver.name());
                path = path.replaceAll("%t", time);
                path = path.replaceAll("%i", Integer.toString(FILE_ID++));
                path = path.replaceAll("%g", Integer.toString(goal.node()
                                .serialNr()));

                return path;
        }

		
		public void addWarning(SolverType type) {
			StringBuffer message = new StringBuffer();
			message.append("You are using a version of "+type.getName()+
					         " which has not been tested for this version of KeY.\nIt can therefore be that" +
					         " errors occur that would not occur\nusing " +
					         (type.getSupportedVersions().length > 1 ? 
					         "one of the following versions:\n" :
					        	 "the following version:\n"));
			for (String v: type.getSupportedVersions()){
			    message.append(v + ", ");
			}
			message.deleteCharAt(message.lastIndexOf(","));
			
			progressDialog.addInformation("Warning: Your version of "+type.toString()+" may not be supported by KeY.", Color.ORANGE,message.toString());			
				
		
		}
		
		private class ProgressDialogListenerImpl implements ProgressDialogListener {
            
			
			
            private SolverLauncher launcher;
            private boolean counterexample;
            
            

			public ProgressDialogListenerImpl(SolverLauncher launcher,
					boolean counterexample) {
				super();
				this.launcher = launcher;
				this.counterexample = counterexample;
			}

			@Override
            public void infoButtonClicked(int column, int row) {
                    InternSMTProblem problem = getProblem(column, row);
                    showInformation(problem);
                    
            }
            
            @Override
            public void stopButtonClicked() {
               
                    stopEvent(launcher); 
            }
            
            @Override
            public void applyButtonClicked() {
                    applyEvent(launcher);
                    
            }

            @Override
            public void discardButtonClicked() {
                    discardEvent(launcher);
                    //remove semantics blasting proof for ce dialog
                    if(counterexample){
                    	MainWindow mw = MainWindow.getInstance();
                        KeYMediator mediator = mw.getMediator();
                    	mediator.getUI().removeProof(mediator.getSelectedProof());
                    }
                    
            }

            @Override
            public void additionalInformationChosen(Object obj) {
            	  if(obj instanceof String){
            		  JOptionPane.showOptionDialog(progressDialog,
                              obj,
                              "Warning",
                              JOptionPane.DEFAULT_OPTION,
                              JOptionPane.WARNING_MESSAGE,
                              null,
                              null,
                              null);
              	  }else if(obj instanceof InternSMTProblem){
            		  showInformation((InternSMTProblem)obj);   
            	  }
            }
    };
	


}