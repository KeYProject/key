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

package de.uka.ilkd.key.core;


/**
 * Listener for longer tasks, which may be run in a separate worker thread.
 * Examples: proof loading, processing strategies
 */
public interface ProverTaskListener {
    /**
     * Called when a task is started.
     * @param message a description of the task, example: "Processing Strategy"
     * @param size indicates the amount of work needed to complete the task,
     * used to display a progress bar. Pass 0 to indicate unknown size.
     */
    void taskStarted ( String message, int size );
    
    /**
     * Called when progress is made on a task.
     * 
     * This method is called after every single step of the task
     * 
     * @param position
     *            indicates how much work has been done relative to the value of
     *            {@code size} passed in {@link #taskStarted(String, int)}.
     */
    void taskProgress ( int position );
    
    
    /**
     * Called when a task is finished.
     * @param info a TaskFinishedInfo object with additional information
     */
    void taskFinished (TaskFinishedInfo info);
}