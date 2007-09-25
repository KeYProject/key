// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit;

/**
 * A UnitListener is given to the unit manager to 
 * log the loading and operation activities.
 * 
 * The loading activity is cut in major and minor steps.
 * - the major steps are kind of activity: opening files, loading asttrees,
 *   loading namespaces, etc....
 * - the minor steps are each step in each of the susmentionned activities.
 * @see TextUnitListener
 * @see 
 */
public interface UnitListener {

    

    /**
     * to begin logging 
     * we do not need a integer in this case.
     */
    void beginLogging();
    
    /**
     * to pause the logging activity. the progress 
     * activity is not garantied to be consistent
     * if the logging is paused during the loading
     * process.
     */
    void pauseLogging();

    /**
     * to end the logging activity.
     */
    void stopLogging();
    
    /**
     * to begin the logging of the loading process begins.
     * @param major the number of "big" steps for the loading process; usefull for 
     *              showing progression of the loading process to the user.
     *
     */
    void loadingInitialLogEntry(String message, int major);

    /**
     * used when logging a major step in the loading process;
     * @param message the log entry
     * @param minor the number of intermediate minor steps
     */
    void loadingMajorLogEntry(String message, int minor);
    
    /**
     * used when loading a major step that does not need
     * intermediate steps.
     * @param message the log entry
     */
    void loadingMajorLogEntry(String message);

    /**
     * for logging a minor step in the loading
     * process.
     * @param message the log entry
     */
    void loadingMinorLogEntry(String message);

    /** 
     * for logging operational activity
     * @param message the log entry
     */
    void operationLogEntry(String message);
    
}
