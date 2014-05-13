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

package org.key_project.util.eclipse;

import java.io.File;

/**
 * Provides utility methods for the application itself.
 * @author Martin Hentschel
 */
public final class ApplicationUtil {
   /**
    * <p>
    * Eclipse parameter to hide the splash screen.
    * </p>
    * <p>
    * see <a href="http://help.eclipse.org/galileo/topic/org.eclipse.platform.doc.isv/reference/misc/runtime-options.html">http://help.eclipse.org/galileo/topic/org.eclipse.platform.doc.isv/reference/misc/runtime-options.html</a>
    * </p>
    */
   public static final String ECLIPSE_PARAMETER_NO_SPLASH = "-noSplash";
   
   /**
    * Forbid instances.
    */
   private ApplicationUtil() {
   }
   
   /**
    * Returns the path and name of the java launcher in which this program is executed.
    * @return The path and name of the java launcher in which this program is executed.
    */
   public static String getJavaLauncher() {
      final String launcher = "java";
      String java = System.getProperty("sun.boot.library.path");
      if (java != null && !java.isEmpty()) {
         File folder = new File(java);
         if (folder.isDirectory()) {
            return new File(folder, launcher).getAbsolutePath();
         }
         else {
            return launcher;
         }
      }
      else {
         return launcher;
      }
   }

   /**
    * Returns the path to the launcher which has started this application.
    * @return The path to the launcher which has started this application.
    */
   public static File getLauncher() {
      String path = System.getProperty("-launcher");
      if (path != null) {
         return new File(path);
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the name of the launcher which has started this application.
    * @return The name of the launcher which has started this application.
    */
   public static String getLauncherName() {
      File launcher = getLauncher();
      return launcher != null ? launcher.getName() : null;
   }
}