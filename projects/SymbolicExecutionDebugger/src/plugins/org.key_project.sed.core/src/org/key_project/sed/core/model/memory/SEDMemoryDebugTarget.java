package org.key_project.sed.core.model.memory;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.impl.AbstractSEDDebugTarget;

/**
 * Implementation of {@link ISEDDebugTarget} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEDMemoryDebugTarget extends AbstractSEDDebugTarget {
   /**
    * The contained {@link ISEDThread}s.
    */
   private List<ISEDThread> threads = new LinkedList<ISEDThread>();
   
   /**
    * Constructor.
    * @param launch The {@link ILaunch} in that this {@link IDebugTarget} is used.
    */
   public SEDMemoryDebugTarget(ILaunch launch) {
      super(launch);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDThread[] getSymbolicThreads() throws DebugException {
      return threads.toArray(new ISEDThread[0]);
   }
   
   /**
    * Adds a new {@link ISEDThread}.
    * @param thread The {@link ISEDThread} to add.
    */
   public void addSymbolicThread(ISEDThread thread) {
      if (thread != null) {
         threads.add(thread);
      }
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public void setModelIdentifier(String modelIdentifier) {
      super.setModelIdentifier(modelIdentifier);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public void setName(String name) {
      super.setName(name);
   }
}
