/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.util.java;

import java.lang.reflect.InvocationTargetException;

import javax.swing.SwingUtilities;

import org.eclipse.swt.widgets.Display;

/**
 * Provides static methods to work with Swing.
 * @author Martin Hentschel
 */
public final class SwingUtil {
    /**
     * Forbid instances.
     */
    private SwingUtil() {
    }
    
    /**
     * Executes the {@link Runnable} in the {@link Thread} of Swing asynchronous.
     * @param run The {@link Runnable} to execute.
     * @throws InterruptedException Occurred Exception.
     * @throws InvocationTargetException Occurred Exception.
     */
    public static void invokeLater(Runnable run) throws InterruptedException, InvocationTargetException {
        SwingUtilities.invokeLater(run);
    }

    /**
     * Checks if the currently active {@link Thread} is responsible
     * for the Swing UI.
     * @return {@code true} is Swing {@link Thread}, {@code false} is not Swing {@link Thread}.
     */
    public static boolean isSwingThread() {
       return SwingUtilities.isEventDispatchThread();
    }

    /**
     * <p>
     * Executes the {@link Runnable} in the {@link Thread} of Swing synchronous.
     * </p>
     * <p>
     * <b>Attention: </b> It is not possible to use this method from
     * Thread of the {@link Display}. In this case an {@link InterruptedException}
     * is thrown.
     * </p>
     * <p>
     * For informations about SWT and Swing integration have a look at:
     * <ul>
     *    <li><a href="http://www.eclipsezone.com/eclipse/forums/t45697.html">http://www.eclipsezone.com/eclipse/forums/t45697.html</li>
     *    <li><a href="http://www.eclipse.org/articles/article.php?file=Article-Swing-SWT-Integration/index.html">http://www.eclipse.org/articles/article.php?file=Article-Swing-SWT-Integration/index.html</li>
     * </ul> 
     * </p>
     * @param run The {@link Runnable} to execute.
     * @throws InterruptedException Occurred Exception.
     * @throws InvocationTargetException Occurred Exception.
     */
    public static void invokeAndWait(Runnable run) throws InterruptedException, InvocationTargetException {
        if (run != null) {
            if (isSwingThread()) {
                run.run();
            }
            else {
               if (Display.getCurrent() == null) {
                  SwingUtilities.invokeAndWait(run);
               }
               else {
                  throw new InterruptedException("Synchronous invokation is not possible from display's thread.");
//                  RunnableLock lock = new RunnableLock(run);
//                  SwingUtilities.invokeLater(lock);
//                  while (!lock.done()) {
//                      // Attention: By default is it not possible to execute
//                      // synchronous messages between SWT and Swing Thread.
//                      // Also a manual lock with Object#wait() and
//                      // Object#notify() causes a deadlock on Mac OS.
//                      // The only solution is to keep the event handling alive
//                      // in the SWT thread while it waits for the Swing thread.
//                      if (!Display.getDefault().readAndDispatch()) {
//                          Display.getDefault().sleep();
//                      }
//                  }
               }
            }
        }
    }
    
//    /**
//     * Helper class that is used to determine when the wrapped
//     * {@link Runnable} is completely executed.
//     * @author Martin Hentschel
//     */
//    private static class RunnableLock implements Runnable {
//        /**
//         * The child {@link Runnable} to execute.
//         */
//        private Runnable run;
//        
//        /**
//         * Constructor.
//         * @param run The child {@link Runnable} to execute.
//         */
//        public RunnableLock(Runnable run) {
//            super();
//            this.run = run;
//        }
//
//        /**
//         * Checks if the execution is completed.
//         * @return {@code true} execution completed, {@code false} still in execution or execution was not started.
//         */
//        public boolean done() {
//            return run == null;
//        }
//
//        /**
//         * {@inheritDoc}
//         */
//        @Override
//        public void run() {
//            if (run != null) {
//                run.run();
//            }
//            run = null;
//        }
//    }
}