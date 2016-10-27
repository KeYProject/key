package org.key_project.sed.key.core.model;

import org.eclipse.core.runtime.Assert;
import org.key_project.sed.core.model.ISENodeLink;
import org.key_project.sed.core.model.impl.AbstractSENodeLink;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionLink;

/**
 * Implementation of {@link ISENodeLink} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYNodeLink extends AbstractSENodeLink {
   /**
    * The source {@link IKeYSENode}.
    */
   private IKeYSENode<?> source;
   
   /**
    * The target {@link IKeYSENode}.
    */
   private IKeYSENode<?> target;

   /**
    * The represented {@link IExecutionLink}.
    */
   private final IExecutionLink executionLink;
   
   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget}.
    * @param executionLink The represetned {@link IExecutionLink}.
    */
   public KeYNodeLink(KeYDebugTarget target, IExecutionLink executionLink) {
      super(target);
      this.executionLink = executionLink;
      target.registerLink(this);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public KeYDebugTarget getDebugTarget() {
      return (KeYDebugTarget) super.getDebugTarget();
   }

   /**
    * Returns the represented {@link IExecutionLink}.
    * @return The represented {@link IExecutionLink}.
    */
   public IExecutionLink getExecutionLink() {
      return executionLink;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSENode<?> getSource() {
      return source;
   }

   /**
    * Sets the source {@link IKeYSENode}.
    * @param source The source {@link IKeYSENode} to set.
    */
   public void setSource(IKeYSENode<?> source) {
      Assert.isTrue(this.source == null || this.source == source);
      this.source = source;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSENode<?> getTarget() {
      return target;
   }

   /**
    * Sets the target {@link IKeYSENode}.
    * @param source The target {@link IKeYSENode} to set.
    */
   public void setTarget(IKeYSENode<?> target) {
      Assert.isTrue(this.target == null || this.target == target);
      this.target = target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return null;
   }
}
