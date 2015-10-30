package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.impl.AbstractSEConstraint;

/**
 * Implementation of {@link ISEConstraint} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEMemoryConstraint extends AbstractSEConstraint {
   /**
    * The constraint name.
    */
   private final String name;

   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} in that this element is contained.
    * @param name The constraint name.
    */
   public SEMemoryConstraint(ISEDebugTarget target, String name) {
      super(target);
      this.name = name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setId(String id) {
      super.setId(id);
   }
}
