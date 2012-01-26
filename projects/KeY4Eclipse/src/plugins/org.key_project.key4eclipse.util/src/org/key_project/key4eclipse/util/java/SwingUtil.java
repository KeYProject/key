package org.key_project.key4eclipse.util.java;

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
     * <p>
     * Executes the {@link Runnable} in the {@link Thread} of Swing synchronous.
     * </p>
     * <p>
     * <b>Attention:</b> This method does not work correctly from
     * {@link Display}s Thread on Mac OS. Also {@link Object#wait()}
     * and {@link Object#notify()} don't work in this scenario.
     * </p>
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
