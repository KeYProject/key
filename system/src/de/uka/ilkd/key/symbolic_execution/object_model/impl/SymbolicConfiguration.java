// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicConfiguration;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicState;

/**
 * Default implementation of {@link ISymbolicConfiguration}.
 * @author Martin Hentschel
 */
public class SymbolicConfiguration extends AbstractElement implements ISymbolicConfiguration {
   /**
    * The contained {@link ISymbolicEquivalenceClass}.
    */
   private final ImmutableList<ISymbolicEquivalenceClass> equivalenceClasses;
   
   /**
    * The {@link ISymbolicState}.
    */
   private ISymbolicState state;
   
   /**
    * The contained {@link ISymbolicObject}s.
    */
   private ImmutableList<ISymbolicObject> objects = ImmutableSLList.nil();

   /**
    * Constructor.
    * @param equivalenceClasses The provided equivalence classes.
    * @param settings The {@link IModelSettings} to use.
    */
   public SymbolicConfiguration(IModelSettings settings, 
                                ImmutableList<ISymbolicEquivalenceClass> equivalenceClasses) {
      super(settings);
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