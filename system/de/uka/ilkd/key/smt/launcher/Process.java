// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.smt.launcher;

import java.util.Collection;


import de.uka.ilkd.key.smt.MakesProgress;
import de.uka.ilkd.key.smt.SMTProgressMonitor;



public interface Process extends Runnable,MakesProgress {
	void setProcessListener(ProcessListener listener);
	/**
	 * Interrupts the process.
	 */
	void stop();
	/**
	 * @return returns the title of the process. For GUI-Reasons.
	 */
	String getTitle();
	/**
	 * @return <code>true</code> if the process is running, otherwise false.
	 */
	boolean running();
	Collection<SMTProgressMonitor> getMonitors();
	/**
	 * @return the current running time in ms.
	 */
	long getRunningTime();
	void init();
	/**
	 * @return the index of the current cycle. For example the process of an 
	 * external prover returns the number of goal working on.
	 */
	int getCurrentCycle();
	/**
	 * @return The max number of cycles. For example the process of an external provers 
	 * returns the number of goals.
	 */
	int getMaxCycle();
	
	boolean wasSuccessful();

	
}
