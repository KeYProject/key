// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.ui;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.io.File;
import java.util.List;

import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.ApplyTacletDialogModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ProofStarter;

public class ConsoleUserInterface extends AbstractUserInterface {
   public static final String PROP_AUTO_MODE = "autoMode";
   
   /**
    * The used {@link PropertyChangeSupport}.
    */
    private PropertyChangeSupport pcs = new PropertyChangeSupport(this);
    
    private final BatchMode batchMode;
    private final boolean verbose;
	private ProofStarter ps;
	private KeYMediator mediator;
	private boolean autoMode;
	
    public boolean isAutoMode() {
      return autoMode;
   }

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
       boolean oldValue = isAutoMode();
       autoMode = true;
       firePropertyChange(PROP_AUTO_MODE, oldValue, isAutoMode());
    }

    @Override
    public void notifyAutomodeStopped() {
       boolean oldValue = isAutoMode();
       autoMode = false;
       firePropertyChange(PROP_AUTO_MODE, oldValue, isAutoMode());
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
            false, 
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
      if (proof != null) {
         proof.dispose();
      }
   }
   
   /**
    * Returns the used {@link PropertyChangeSupport}.
    * @return the used {@link PropertyChangeSupport}.
    */
   protected PropertyChangeSupport getPcs() {
       return pcs;
   }
   
   /**
    * Adds the given listener.
    * @param listener The listener to add.
    */
   public void addPropertyChangeListener(PropertyChangeListener listener) {
       pcs.addPropertyChangeListener(listener);
   }
   
   /**
    * Adds the given listener for the given property only.
    * @param propertyName The property to observe.
    * @param listener The listener to add.
    */
   public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
       pcs.addPropertyChangeListener(propertyName, listener);
   }
   
   /**
    * Removes the given listener.
    * @param listener The listener to remove.
    */
   public void removePropertyChangeListener(PropertyChangeListener listener) {
       pcs.removePropertyChangeListener(listener);
   }
   
   /**
    * Removes the given listener from the given property.
    * @param propertyName The property to no longer observe.
    * @param listener The listener to remove.
    */
   public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
       pcs.removePropertyChangeListener(propertyName, listener);
   }
   
   /**
    * Fires the event to all available listeners.
    * @param propertyName The property name.
    * @param index The changed index.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void fireIndexedPropertyChange(String propertyName, int index, boolean oldValue, boolean newValue) {
       pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
   }
   
   /**
    * Fires the event to all available listeners.
    * @param propertyName The property name.
    * @param index The changed index.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void fireIndexedPropertyChange(String propertyName, int index, int oldValue, int newValue) {
       pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
   }
   
   /**
    * Fires the event to all available listeners.
    * @param propertyName The property name.
    * @param index The changed index.
    * @param oldValue The old value.
    * @param newValue The new value.
    */    
   protected void fireIndexedPropertyChange(String propertyName, int index, Object oldValue, Object newValue) {
       pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
   }
   
   /**
    * Fires the event to all listeners.
    * @param evt The event to fire.
    */
   protected void firePropertyChange(PropertyChangeEvent evt) {
       pcs.firePropertyChange(evt);
   }
   
   /**
    * Fires the event to all listeners.
    * @param propertyName The changed property.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
       pcs.firePropertyChange(propertyName, oldValue, newValue);
   }
   
   /**
    * Fires the event to all listeners.
    * @param propertyName The changed property.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void firePropertyChange(String propertyName, int oldValue, int newValue) {
       pcs.firePropertyChange(propertyName, oldValue, newValue);
   }
   
   /**
    * Fires the event to all listeners.
    * @param propertyName The changed property.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
       pcs.firePropertyChange(propertyName, oldValue, newValue);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isRegisterProofs() {
      return false;
   }
}