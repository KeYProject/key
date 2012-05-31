package org.key_project.sed.key.core.model;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDDebugNode;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Provides methods each {@link ISEDDebugNode} of the symbolic execution debugger (SED)
 * based on KeY must have.
 * @author Martin Hentschel
 */
public interface IKeYSEDDebugNode<E extends IExecutionNode> extends ISEDDebugNode {
   /**
    * Returns the represented {@link IExecutionNode}.
    * @return The reprsented {@link IExecutionNode}.
    */
   public E getExecutionNode();
   
   /**
    * {@inheritDoc}
    */
   @Override
   public KeYDebugTarget getDebugTarget();
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSEDDebugNode<?> getParent() throws DebugException;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSEDDebugNode<?>[] getChildren() throws DebugException;
}
