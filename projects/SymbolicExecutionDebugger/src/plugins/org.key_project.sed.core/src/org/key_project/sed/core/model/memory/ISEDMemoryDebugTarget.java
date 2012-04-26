package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Defines the public methods to edit an {@link ISEDDebugTarget} in
 * the main memory.
 * @author Martin Hentschel
 */
public interface ISEDMemoryDebugTarget extends ISEDDebugTarget {
   /**
    * Adds a new {@link ISEDThread}.
    * @param thread The {@link ISEDThread} to add.
    */
   public void addSymbolicThread(ISEDThread thread);

   /**
    * Adds a new {@link ISEDThread}.
    * @param index The index to insert the new thread at.
    * @param thread The {@link ISEDThread} to add.
    */
   public void addSymbolicThread(int index, ISEDThread thread);
   
   /**
    * Removes the child {@link ISEDThread}.
    * @param thread The {@link ISEDThread} to remove.
    */
   public void removeSymbolicThread(ISEDThread thread);
   
   /**
    * Returns the index of the given child {@link ISEDThread}.
    * @param thread The child {@link ISEDThread}.
    * @return The index of the child {@link ISEDThread} or {@code -1} if it is no child.
    */
   public int indexOfSymbolicThread(ISEDThread thread);
}
