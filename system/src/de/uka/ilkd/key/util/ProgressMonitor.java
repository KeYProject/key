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

package de.uka.ilkd.key.util;

/** An interface to some progress reporting mechanism.  the {@link
 * #setMaximum(int)} method must always be called first to determine
 * the number of steps at which the task is finished.  After that,
 * {@link #setProgress} will be called repeatedly to indicate how
 * far one has got.  The progress monitor is assumed to have an
 * internal state in which it remembers the <code>maximum</code> value
 * set by the {@link #setMaximum} method.
 *
 * <p>A more general alternative would be to have tasks accept
 * progress listeners, but we probably don't want more than one
 * progress bar anyway.
 */

public interface ProgressMonitor {

    /** Set the progress achieved so far.  The parameter
     * <code>progress</code> has to be &gt;=0 and &lt;= to the maximum
     * value previously set with {@link ProgressMonitor#setMaximum}.
     * 
     * @param progress number of steps completed */
    void setProgress(int progress);
    
    /** Set the maximum number of steps for this task.
     *
     * @param maximum maximum number of steps, &gt;=0.
     */
    void setMaximum(int maximum);
	
    /** A progress monitor that does nothing.  This
     * is a singleton, use {@link ProgressMonitor.Empty#getInstance} to get one. */
    public static class Empty implements ProgressMonitor {

	private Empty() {}

	private static Empty INSTANCE = new Empty();

	/** Return a do-nothing progress monitor. */
	public static Empty getInstance() {
	    return INSTANCE;
	}

	public void setProgress(int progress) {}
	
	public void setMaximum(int maximum) {}

    }
}