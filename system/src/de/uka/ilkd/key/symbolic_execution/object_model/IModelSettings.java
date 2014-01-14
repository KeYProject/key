package de.uka.ilkd.key.symbolic_execution.object_model;

/**
 * Provides the settings used to construct a symbolic object model.
 * @author Martin Hentschel
 */
public interface IModelSettings {
   /**
    * Checks if pretty printing is used or not.
    * @return {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   public boolean isUsePrettyPrinting();
}
