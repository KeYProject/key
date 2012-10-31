package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicState;

/**
 * <p>
 * Represents the symbolic state of an {@link ISymbolicConfiguration}.
 * </p>
 * <p>
 * The default implementation is {@link SymbolicState}.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicState
 */
public interface ISymbolicState extends ISymbolicAssociationValueContainer {
   /**
    * Returns the name of this state.
    * @return The name of this state.
    */
   public String getName();
}