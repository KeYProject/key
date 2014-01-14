package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;

/**
 * Default implementation of {@link IModelSettings}.
 * @author Martin Hentschel
 */
public class ModelSettings implements IModelSettings {
   /**
    * {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   private final boolean usePrettyPrinting;

   /**
    * Constructor.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   public ModelSettings(boolean usePrettyPrinting) {
      this.usePrettyPrinting = usePrettyPrinting;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isUsePrettyPrinting() {
      return usePrettyPrinting;
   }
}
