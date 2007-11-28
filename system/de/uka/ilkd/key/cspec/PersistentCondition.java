// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/** $Id: PersistentCondition.java 1.4.1.1 Tue, 26 Jun 2007 10:47:12 +0200 christian $
 * @(#)$RCSfile$ 1.1 2003-02-10 Andre Platzer
 *
 * Copyright (c) 2003 Andre Platzer. All Rights Reserved.
 */

package de.uka.ilkd.key.cspec;

/**
 * Implementation of persistent conditions, i.e. conditions that do
 * not suffer from signal loss.  Note that this concept can be
 * generalized beyond the limitations of our current implementation.
 * However, we do not yet have any needs for more sophisticated
 * conditions.
 *
 * @author Andr&eacute; Platzer
 * @version 1.1, 2003-02-10
 * @version-revision $Revision: 1.4.1.1 $, $Date: Tue, 26 Jun 2007 10:47:12 +0200 $
 */
public class PersistentCondition {
    private final Object synchronization;
    private int count;
    /**
     * Create a new condition.
     */
    public PersistentCondition() {
	//@internal note that we do not need synchronization, here, since the constructor has not yet returned
	count = 0;
	synchronization = new Object();
    }

    /**
     * Signal that this condition has become true.
     * @see Object#notifyAll()
     */
    public void signal() {
	synchronized (synchronization) {
	    count = count + 1;
	    synchronization.notifyAll();
	}
    }
    
    /**
     * Wait until the condition is true.
     * If the condition has not yet become true due to an earlier call to
     * {@link #signal()}, this method will wait until {@link #signal()} gets called.
     * @throws InterruptedException if another thread has interrupted
     * the current thread. The interrupted status of the current
     * thread is cleared when this exception is thrown.
     * @see Object#wait()
     */
    public void waitFor() throws InterruptedException {
	synchronized (synchronization) {
	    if (count > 0)
		return;
	    else
		synchronization.wait();
	}
    }
}// PersistentCondition
