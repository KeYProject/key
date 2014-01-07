package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

/**
 * The default implementation of {@link ITreeSettings}.
 * @author Martin Hentschel
 */
public class TreeSettings implements ITreeSettings {
   /**
    * {@code true} merge branch conditions which means that a branch condition never contains another branch condition
    * or {@code false} allow that branch conditions contains branch conditions.
    */
   private final boolean mergeBranchConditions;
   
   /**
    * {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   private final boolean usePrettyPrinting;

   /**
    * Constructor.
    * @param mergeBranchConditions {@code true} merge branch conditions which means that a branch condition never contains another branch condition
    * or {@code false} allow that branch conditions contains branch conditions.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   public TreeSettings(boolean mergeBranchConditions, boolean usePrettyPrinting) {
      this.mergeBranchConditions = mergeBranchConditions;
      this.usePrettyPrinting = usePrettyPrinting;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isMergeBranchConditions() {
      return mergeBranchConditions;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isUsePrettyPrinting() {
      return usePrettyPrinting;
   }
}
