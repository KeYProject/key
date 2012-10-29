package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicState;

/**
 * Default implementation of {@link ISymbolicState}.
 * @author Martin Hentschel
 */
public class SymbolicState extends AbstractSymbolicAssociationValueContainer implements ISymbolicState {
   /**
    * The name of this state.
    */
   private String name;

   /**
    * Constructor.
    * @param name The name of this state.
    */
   public SymbolicState(String name) {
      super();
      this.name = name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return name;
   }
}