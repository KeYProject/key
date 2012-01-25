/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.example.util;

import org.key_project.key4eclipse.util.eclipse.Logger;

import de.hentschel.visualdbc.example.Activator;

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
