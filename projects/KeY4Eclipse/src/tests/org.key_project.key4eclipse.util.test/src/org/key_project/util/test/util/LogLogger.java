package org.key_project.util.test.util;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.ILogListener;
import org.eclipse.core.runtime.IStatus;

/**
 * Implementation of {@link ILogListener} that stores all added logs
 * in the main memory.
 * @author Martin Hentschel
 */
public class LogLogger implements ILogListener {
   /**
    * The caught logs.
    */
   private Map<String, List<IStatus>> log = new HashMap<String, List<IStatus>>();

   /**
    * {@inheritDoc}
    */
   @Override
   public void logging(IStatus status, String plugin) {
      List<IStatus> list = log.get(plugin);
      if (list == null) {
         list = new LinkedList<IStatus>();
         log.put(plugin, list);
      }
      list.add(status);
   }

   /**
    * Returns all caught logs.
    * @return The caught logs.
    */
   public Map<String, List<IStatus>> getLog() {
      return log;
   }
}
