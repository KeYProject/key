package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociationValueContainer;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;

/**
 * Default implementation of {@link ISymbolicAssociationValueContainer}.
 * @author Martin Hentschel
 */
public abstract class AbstractSymbolicAssociationValueContainer implements ISymbolicAssociationValueContainer {
   /**
    * The contained {@link ISymbolicAssociation}s.
    */
   private ImmutableList<ISymbolicAssociation> associations = ImmutableSLList.nil();
   
   /**
    * The contained {@link ISymbolicValue}s.
    */
   private ImmutableList<ISymbolicValue> values = ImmutableSLList.nil();

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<ISymbolicAssociation> getAssociations() {
      return associations;
   }
   
   /**
    * Adds a new {@link ISymbolicAssociation}.
    * @param value The new {@link ISymbolicAssociation} to add.
    */
   public void addAssociation(ISymbolicAssociation association) {
      associations = associations.append(association);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<ISymbolicValue> getValues() {
      return values;
   }
   
   /**
    * Adds a new {@link ISymbolicValue}.
    * @param value The new {@link ISymbolicValue} to add.
    */
   public void addValue(ISymbolicValue value) {
      values = values.append(value);
   }
}