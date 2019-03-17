package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionLink;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * The default implementation of {@link IExecutionLink}.
 * @author Martin Hentschel
 */
public class ExecutionLink implements IExecutionLink {
   /**
    * The source {@link IExecutionNode}.
    */
   private final IExecutionNode<?> source;
   
   /**
    * The target {@link IExecutionNode}.
    */
   private final IExecutionNode<?> target;

   /**
    * Constructor.
    * @param source The source {@link IExecutionNode}.
    * @param target The target {@link IExecutionNode}.
    */
   public ExecutionLink(IExecutionNode<?> source, IExecutionNode<?> target) {
      this.source = source;
      this.target = target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionNode<?> getSource() {
      return source;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionNode<?> getTarget() {
      return target;
   }
}
