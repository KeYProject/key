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
     * Executes the {@link Runnable} in the {@link Thread} of Swing asynchronous.
     * @param run The {@link Runnable} to execute.
     * @throws InterruptedException Occurred Exception.
     * @throws InvocationTargetException Occurred Exception.
     */
    public static void invokeLater(Runnable run) throws InterruptedException, InvocationTargetException {
        SwingUtilities.invokeLater(run);
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
     * <p>
     * More informations about SWT and Swing integration have a look at:
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
            if (SwingUtilities.isEventDispatchThread()) {
                run.run();
            }
            else {
                RunnableLock lock = new RunnableLock(run);
                SwingUtilities.invokeLater(lock);
                while (!lock.done()) {
                    if (!Display.getDefault().readAndDispatch()) {
                        Display.getDefault().sleep();
                    }
                }
            }
        }
    }
    
    private static class RunnableLock implements Runnable {
        private Runnable run;
        
        private RunnableLock(Runnable run) {
            super();
            this.run = run;
        }

        public boolean done() {
            return run == null;
        }

        @Override
        public void run() {
            if (run != null) {
                run.run();
            }
            run = null;
        }
    }
}
