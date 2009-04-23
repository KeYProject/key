// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//This file is part of KeY - Integrated Deductive Software Design 
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

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
     * @param position indicates how much work has been done relative to the
     * value of size passed in @c taskStarted
     */
    void taskProgress ( int position );
    
    /**
     * Called when a task is finished.
     * @param info a TaskFinishedInfo object with additional information
     */
    void taskFinished (TaskFinishedInfo info);
}
