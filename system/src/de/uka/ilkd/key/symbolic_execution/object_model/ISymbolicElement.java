package de.uka.ilkd.key.symbolic_execution.object_model;

/**
 * Defines the basic methods and properties each element in an
 * symbolic object model has to have.
 * @author Martin Hentschel
 */
public interface ISymbolicElement {
   /**
    * Returns the {@link IModelSettings} to use.
    * @return The {@link IModelSettings} to use.
    */
   public IModelSettings getSettings();
}
