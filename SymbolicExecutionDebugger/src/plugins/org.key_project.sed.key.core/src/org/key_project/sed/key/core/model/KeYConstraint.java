package org.key_project.sed.key.core.model;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.impl.AbstractSEConstraint;
import org.key_project.sed.key.core.util.LogUtil;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;

/**
 * Implementation of {@link ISEConstraint} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYConstraint extends AbstractSEConstraint {
   /**
    * The {@link IExecutionConstraint} to represent by this {@link ISEConstraint}.
    */
   private final IExecutionConstraint executionConstraint;

   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} in that this element is contained.
    * @param executionConstraint The {@link IExecutionConstraint} to represent by this {@link ISEConstraint}.
    */
   public KeYConstraint(ISEDebugTarget target, IExecutionConstraint executionConstraint) {
      super(target);
      Assert.isNotNull(executionConstraint);
      this.executionConstraint = executionConstraint;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      try {
         return executionConstraint.getName();
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
   }

   /**
    * Returns the represented {@link IExecutionConstraint}.
    * @return The represented {@link IExecutionConstraint}.
    */
   public IExecutionConstraint getExecutionConstraint() {
      return executionConstraint;
   }
}
