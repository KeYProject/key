// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui;

import java.io.File;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reuse.ReusePoint;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ProgressMonitor;

/**
 * This class is an example how to implement the IMain interface. It offers
 * a simple prover interface allowing to load and prove exactly one problem.
 */
public class SimpleStarter implements IMain {

    private KeYMediator mediator;
    private String fileNameOnStartUp;
    private ProverTaskListener ptl;

    public SimpleStarter(String file) {
	this.fileNameOnStartUp = file;
        this.ptl= new MainTaskListenerBatchMode();
    }
    
    public SimpleStarter(String file, ProverTaskListener ptl ) {
        this.fileNameOnStartUp = file;
        this.ptl = ptl;
    }
    
    public void setKeYMediator(KeYMediator mediator) {
        this.mediator = mediator;
        this.mediator.setSimplifier(ProofSettings.DEFAULT_SETTINGS
                .getSimultaneousUpdateSimplifierSettings().getSimplifier());
    }
    
    public void addProblem(final de.uka.ilkd.key.proof.ProofAggregate plist) {
        Runnable guiUpdater = new Runnable() {
            public void run() {
                setUpNewProof(plist.getFirstProof());
            }
        };
        if (SwingUtilities.isEventDispatchThread())
            guiUpdater.run();
        else
            KeYMediator.invokeAndWait(guiUpdater);
    }
    
    protected Proof setUpNewProof(Proof proof) {
        mediator.setProof(proof);
        return proof;
    }
    

    public void closeTaskWithoutInteraction() {
        System.out.println("Proof:" + mediator.getSelectedProof().closed() );
        System.out.println("Nodes:" + mediator.getSelectedProof().countNodes() );
    }

    public String getInternalVersion() {
        return "xyz";
    }

    public ProgressMonitor getProgressMonitor() {
        return new ProgressMonitor() {

            public void setMaximum(int maximum) {
                // TODO Auto-generated method stub
                
            }

            public void setProgress(int progress) {
                // TODO Auto-generated method stub
                
            }
            
        };
    }

    public void loadCommandLineFile() {
        if (fileNameOnStartUp != null) {
            loadProblem(new File(fileNameOnStartUp));
        }        
    }

    protected void loadProblem(File file) {
        final ProblemLoader pl = 
            new ProblemLoader(file, this, mediator.getProfile(), false);
        pl.addTaskListener(ptl);
        pl.run();
    }
    
    public KeYMediator mediator() {
        return mediator;
    }

    public void setStandardStatusLine() {
        // TODO Auto-generated method stub
        
    }

    public void setStatusLine(String s, int totalChars) {
        //System.out.println(s + ":" + totalChars);
        
    }

    public void setStatusLine(String s) {
     //   System.out.println(s);
    }

    public static void main(String[] args) {
        SimpleStarter key = new SimpleStarter(args[0]);
        key.setKeYMediator(new KeYMediator(key));
        key.loadCommandLineFile();
    }

    public ProverTaskListener getProverTaskListener() {       
        return ptl;
    }

    public void notify(NotificationEvent event) {
        // TODO Auto-generated method stub
        
    }

    public void indicateNoReuse() {
        // TODO Auto-generated method stub
        
    }

    public void indicateReuse(ReusePoint bestReusePoint) {
    }
 
    private void finishedBatchMode (Object result, 
            Proof proof, long time, int appliedRules) {

        System.out.println(proof.closed());
        System.out.println(appliedRules);
        System.out.println(time);
        System.exit(0);
    }
    
    class MainTaskListenerBatchMode implements ProverTaskListener { // XXX
        public void taskStarted(String message, int size) {
            //System.out.println(message + (size > 0 ? 
             //       " (expected dots: " + size + ")" : "" ));
        }
        
        public void taskProgress(int position) {
            //System.out.print(".");
        }
        
        public void taskFinished(TaskFinishedInfo info) {
            System.out.println("DONE.");
            if (info.getSource() instanceof ApplyStrategy) {
                finishedBatchMode(info.getResult(), 
                        info.getProof(), info.getTime(), 
                        info.getAppliedRules());
                Debug.fail ( "Control flow should not reach this point." );
            } else if (info.getSource() instanceof ProblemLoader) {
                if (!"".equals(info.getResult())) {
                    System.out.println(info.getResult());    
                    System.exit(-1);
                }
                if (info.getProof().openGoals().size()==0) {
                    System.out.println("proof.openGoals.size=" + 
                            info.getProof().openGoals().size());
                    System.exit(0);
                }
                mediator.getProof().getActiveStrategy();         
                mediator.startAutoMode();
            }
        }
    }
    
}
