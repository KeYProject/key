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
import static de.uka.ilkd.key.gui.Main.Verbosity.*;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.ApplyTacletDialogModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ProofStarter;

public class ConsoleUserInterface extends AbstractUserInterface {
    private static final int PROGRESS_BAR_STEPS = 50;
    private static final String PROGRESS_MARK = ">";

    public static final String PROP_AUTO_MODE = "autoMode";

   /**
    * The used {@link PropertyChangeSupport}.
    */
    private PropertyChangeSupport pcs = new PropertyChangeSupport(this);

    private final BatchMode batchMode;
    private final byte verbosity;
	private ProofStarter ps;
	private KeYMediator mediator;
	private boolean autoMode;

	// for a progress bar
	private int progressMax = 0;

    public boolean isAutoMode() {
      return autoMode;
   }

   public ConsoleUserInterface(BatchMode batchMode, byte verbosity) {
    	this.batchMode = batchMode;
    	this.verbosity = verbosity;
        this.mediator  = new KeYMediator(this);
    }

   public ConsoleUserInterface(BatchMode batchMode, boolean verbose) {
       this(batchMode, verbose? DEBUG: NORMAL);
   }

    public void taskFinished(TaskFinishedInfo info) {
        progressMax = 0; // reset progress bar marker
        final int openGoals = info.getProof().openGoals().size();
        final Object result2 = info.getResult();
        if (info.getSource() instanceof ApplyStrategy) {
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
                    System.out.println("Time: "+stat.autoModeTime+"ms");
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

            // setInteractive(false) has to be called because the ruleAppIndex
            // has to be notified that we work in auto mode (CS)
            mediator.setInteractive(false);

            final Object result = ps.start();
            if (verbosity >= HIGH) {
            	System.out.println(result);
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
        // TODO Implement ProblemInitializerListener.proofCreated
        // XXX WHY AT THE MAINWINDOW?!?!
    	ps = new ProofStarter(this);
        ps.init(proofAggregate);
        mediator.setProof(proofAggregate.getFirstProof());
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
   public ProblemInitializer createProblemInitializer(Profile profile) {
      ProblemInitializer pi = new ProblemInitializer(this,
            new Services(profile, mediator.getExceptionHandler()),
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