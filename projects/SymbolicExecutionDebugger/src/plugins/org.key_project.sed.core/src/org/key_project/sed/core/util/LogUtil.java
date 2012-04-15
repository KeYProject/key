package org.key_project.sed.core.util;

import org.key_project.sed.core.Activator;
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
