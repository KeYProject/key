/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.key4eclipse.starter.core.util;

import org.key_project.key4eclipse.starter.core.Activator;
import org.key_project.util.eclipse.Logger;

/**
 * Provides static methods for logging.
 * @author Martin Hentschel
 */
public final class LogUtil {
   /**
    * The default {@link Logger} instance.
    */
   private static Logger logger;
   
   /**
    * Forbid instances.
    */
   private LogUtil() {
   }
   
   /**
    * Returns the default {@link Logger} instance for this plug-in.
    * @return The default {@link Logger} instance for this plug-in.
    */
   public static Logger getLogger() {
      if (logger == null) {
         logger = new Logger(Activator.getDefault(), Activator.PLUGIN_ID);
      }
      return logger;
   }
}