// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.util.ProgressMonitor;

/** 
 * This interface extracts method signatures from the original main class
 * that need (currently) to be implemented by a class that wants to represent 
 * an interface to the KeY prover. 
 * 
 * It is a first step to a better separation between GUI and prover.
 */
public interface IMain {

    public abstract String getInternalVersion();

    /**
     * return the mediator
     * 
     * @return the mediator
     */
    public abstract KeYMediator mediator();

    /**
     * Make the status line display a standard message, make progress bar and abort button invisible
     */
    public abstract void setStandardStatusLine();

    /**
     * Display the given message in the status line, make progress bar and abort button visible, set
     * the progress bar range to the given value, set the current progress to zero
     */
    public abstract void setStatusLine(String s, int totalChars);

    /**
     * Display the given message in the status line, make progress bar and abort button invisible
     */
    public abstract void setStatusLine(String s);

    /**
     * Get the progress monitor that will update a progress bar in a corner of the main window.
     */
    public abstract ProgressMonitor getProgressMonitor();

    /**
     * abandons the current active proof immediately without asking for
     * explicit confirmation
     */
    public abstract void closeTaskWithoutInteraction();

    /**
     * adds a new task group to the list of known tasks
     * @param plist a ProofAggregate with a number of problems 
     */
    public abstract void addProblem(
            final de.uka.ilkd.key.proof.ProofAggregate plist);

    /**
     * loads a problem given as command line argument
     */
    public abstract void loadCommandLineFile();

    /**
     * returns a listener to current prover taks
     * @return the prover task listener 
     */
    public abstract ProverTaskListener getProverTaskListener();

    /**
     * receives a notification event and hands it over to the Notification
     * manager
     * @param event the NotificationEvent
     */
    public abstract void notify(NotificationEvent event);
}
