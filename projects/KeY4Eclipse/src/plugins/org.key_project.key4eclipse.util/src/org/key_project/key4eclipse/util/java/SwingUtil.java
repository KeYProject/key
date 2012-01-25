package org.key_project.key4eclipse.util.java;

import java.lang.reflect.InvocationTargetException;

import javax.swing.SwingUtilities;

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
     * Executes the {@link Runnable} in the {@link Thread} of Swing synchron.
     * @param run The {@link Runnable} to execute.
     * @throws InterruptedException Occurred Exception.
     * @throws InvocationTargetException Occurred Exception.
     */
    public static void invokeAndWait(Runnable run) throws InterruptedException, InvocationTargetException {
        if (run != null) {
            if (SwingUtilities.isEventDispatchThread()) {
                run.run();
            }
            else {
                SwingUtilities.invokeAndWait(run);
            }
        }
    }
    
    /**
     * Executes the {@link Runnable} in the {@link Thread} of Swing asynchronous.
     * @param run The {@link Runnable} to execute.
     * @throws InterruptedException Occurred Exception.
     * @throws InvocationTargetException Occurred Exception.
     */
    public static void invokeLater(Runnable run) throws InterruptedException, InvocationTargetException {
        if (run != null) {
            if (SwingUtilities.isEventDispatchThread()) {
                run.run();
            }
            else {
                SwingUtilities.invokeLater(run);
            }
        }
    }
}
