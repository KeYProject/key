package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicConfiguration;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicState;

/**
 * Default implementation of {@link ISymbolicConfiguration}.
 * @author Martin Hentschel
 */
public class SymbolicConfiguration implements ISymbolicConfiguration {
   /**
    * The {@link ISymbolicState}.
    */
   private ISymbolicState state;
   
   /**
    * The contained {@link ISymbolicObject}s.
    */
   private ImmutableList<ISymbolicObject> objects = ImmutableSLList.nil();

   /**
    * The contained {@link ISymbolicEquivalenceClass}.
    */
   private ImmutableList<ISymbolicEquivalenceClass> equivalenceClasses;

   /**
    * Constructor.
    * @param equivalenceClasses The provided equivalence classes.
    */
   public SymbolicConfiguration(ImmutableList<ISymbolicEquivalenceClass> equivalenceClasses) {
      assert equivalenceClasses != null;
      this.equivalenceClasses = equivalenceClasses;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISymbolicState getState() {
      return state;
   }

   /**
    * Sets the {@link ISymbolicState}.
    * @param state The {@link ISymbolicState} to set.
    */
   public void setState(ISymbolicState state) {
      this.state = state;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<ISymbolicObject> getObjects() {
      return objects;
   }
   
   /**
    * Adds a new {@link ISymbolicObject}.
    * @param value The new {@link ISymbolicObject} to add.
    */
   public void addObject(ISymbolicObject object) {
      objects = objects.append(object);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<ISymbolicEquivalenceClass> getEquivalenceClasses() {
      return equivalenceClasses;
   }
}