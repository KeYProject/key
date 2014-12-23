package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEDConstraint;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.impl.AbstractSEDConstraint;

/**
 * Implementation of {@link ISEDConstraint} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEDMemoryConstraint extends AbstractSEDConstraint {
   /**
    * The constraint name.
    */
   private final String name;

   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this element is contained.
    * @param name The constraint name.
    */
   public SEDMemoryConstraint(ISEDDebugTarget target, String name) {
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
