/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.util;

import java.awt.EventQueue;
import java.lang.reflect.InvocationTargetException;
import javax.swing.SwingUtilities;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

@NullMarked
public final class ThreadUtilities {
    private static final Logger LOGGER = LoggerFactory.getLogger(ThreadUtilities.class);

    private ThreadUtilities() {
    }

    /**
     * Invoke a runnable object on the AWT event thread and wait for the execution to finish.
     *
     * If an exception occurs during the run, the trace is printed to stderr.
     *
     * @param runner Runnable capturing code to execute on the awt thread.
     */
    public static void invokeAndWait(Runnable runner) {
        if (SwingUtilities.isEventDispatchThread()) {
            runner.run();
        } else {
            try {
                SwingUtilities.invokeAndWait(runner);
            } catch (InterruptedException e) {
                LOGGER.debug("", e);
            } catch (InvocationTargetException ite) {
                Throwable targetExc = ite.getTargetException();
                LOGGER.debug("", ite);
                if (targetExc != null) {
                    // invocation target exceptions always carry the wrapped failure
                    LOGGER.debug("", targetExc);
                }
            }
        }
    }

    /**
     * Invoke a runnable object on the AWT event thread. Does not wait necessarily for it to finish.
     * If the current thread is already the event queue, the {@link Runnable} object is simply
     * executed.
     *
     * @param runnable Runnable capturing code to execute on the awt thread.
     */
    public static void invokeOnEventQueue(Runnable runnable) {
        if (EventQueue.isDispatchThread()) {
            runnable.run();
        } else {
            SwingUtilities.invokeLater(runnable);
        }
    }

    /**
     * Get all running threads.
     *
     * @return array of threads, some entries may be null
     */
    public static @Nullable Thread[] getThreads() {
        ThreadGroup rootGroup = Thread.currentThread().getThreadGroup();
        if (rootGroup == null) {
            // only a dead thread lacks a thread group; the caller is live
            throw new NullPointerException("No thread group available.");
        }
        ThreadGroup parentGroup;
        while ((parentGroup = rootGroup.getParent()) != null) {
            rootGroup = parentGroup;
        }

        Thread[] threads = new Thread[rootGroup.activeCount() + 1];
        while (rootGroup.enumerate(threads, true) == threads.length) {
            threads = new Thread[threads.length * 2];
        }
        return threads;
    }
}
