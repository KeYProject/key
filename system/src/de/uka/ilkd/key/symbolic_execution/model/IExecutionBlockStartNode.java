package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.SourceElement;

/**
 * An extended {@link IExecutionNode} which groups several child nodes.
 * @author Martin Hentschel
 */
public interface IExecutionBlockStartNode<S extends SourceElement> extends IExecutionNode<S> {
   /**
    * Checks if a block might be opened.
    * @return {@code false} block is definitively not opened, {@code true} block is or might be opened.
    */
   public boolean isBlockOpened();
   
   /**
    * Returns the up to now discovered {@link IExecutionNode}s.
    * @return The up to now discovered {@link IExecutionNode}s.
    */
   public ImmutableList<IExecutionNode<?>> getBlockCompletions();
}
