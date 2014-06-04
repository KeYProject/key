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

package org.key_project.swtbot.swing.util;

import java.lang.reflect.InvocationTargetException;

import javax.swing.SwingUtilities;

import org.eclipse.swt.widgets.Display;

/**
 * Provides utility methods for a save access of Swing.
 * @author Martin Hentschel
 */
public final class SaveSwingUtil {
    /**
     * Forbid instances.
     */
    private SaveSwingUtil() {
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
    public static void invokeAndWait(Runnable run) {
        try {
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
                   }
                }
            }
        } 
        catch (Exception e) {
            throw new RuntimeException("Can't access Swing.", e);
        }
    }
}