package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.AbstractSymbolicAssociationValueContainer;

/**
 * <p>
 * This interface is not instantiated directly because it defines only the
 * common behavior of {@link ISymbolicState} and {@link ISymbolicObject} which
 * is to contain associations (references to other {@link ISymbolicObject}s) 
 * and values (local variables of simple types).
 * </p>
 * <p>
 * The default abstract implementation is {@link AbstractSymbolicAssociationValueContainer}.
 * </p>
 * @author Martin Hentschel
 * @see AbstractSymbolicAssociationValueContainer
 * @see ISymbolicObject
 * @see ISymbolicState
 */
public interface ISymbolicAssociationValueContainer {
   /**
    * Returns the contained associations.
    * @return The contained associations.
    */
   public ImmutableList<ISymbolicAssociation> getAssociations();
   
   /**
    * Returns the contained values.
    * @return The contained values.
    */
   public ImmutableList<ISymbolicValue> getValues();
}