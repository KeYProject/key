package de.uka.ilkd.key.symbolic_execution.model;

/**
 * Provides the settings used to construct the symbolic execution tree.
 * @author Martin Hentschel
 */
public interface ITreeSettings {
   /**
    * Checks if multiple branch conditions are merged or not.
    * @return {@code true} merge branch conditions which means that a branch condition never contains another branch condition
    * or {@code false} allow that branch conditions contains branch conditions.
    */
   public boolean isMergeBranchConditions();

   /**
    * Checks if pretty printing is used or not.
    * @return {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   public boolean isUsePrettyPrinting();
}
