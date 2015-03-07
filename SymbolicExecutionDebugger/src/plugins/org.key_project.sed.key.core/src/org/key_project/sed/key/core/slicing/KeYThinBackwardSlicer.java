package org.key_project.sed.key.core.slicing;

import de.uka.ilkd.key.symbolic_execution.slicing.AbstractSlicer;
import de.uka.ilkd.key.symbolic_execution.slicing.ThinBackwardSlicer;

/**
 * Performs slicing with help of the {@link ThinBackwardSlicer}.
 * @author Martin Hentschel
 */
public class KeYThinBackwardSlicer extends AbstractKeYSlicer {
   /**
    * The name of the implemented slicing algorithm.
    */
   public static final String NAME = "Thin Backward Slicing";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return NAME;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractSlicer createSlicer() {
      return new ThinBackwardSlicer();
   }
}
