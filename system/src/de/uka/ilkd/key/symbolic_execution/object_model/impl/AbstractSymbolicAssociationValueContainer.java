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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociationValueContainer;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;

/**
 * Default implementation of {@link ISymbolicAssociationValueContainer}.
 * @author Martin Hentschel
 */
public abstract class AbstractSymbolicAssociationValueContainer extends AbstractElement implements ISymbolicAssociationValueContainer {
   /**
    * The contained {@link ISymbolicAssociation}s.
    */
   private ImmutableList<ISymbolicAssociation> associations = ImmutableSLList.nil();
   
   /**
    * The contained {@link ISymbolicValue}s.
    */
   private ImmutableList<ISymbolicValue> values = ImmutableSLList.nil();

   /**
    * Constructor.
    * @param settings The {@link IModelSettings} to use.
    */
   public AbstractSymbolicAssociationValueContainer(IModelSettings settings) {
      super(settings);
   }

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
   public ISymbolicAssociation getAssociation(final IProgramVariable programVariable, 
                                              final boolean isArrayIndex, 
                                              final int arrayIndex,
                                              final Term condition) {
      return JavaUtil.search(associations, new IFilter<ISymbolicAssociation>() {
         @Override
         public boolean select(ISymbolicAssociation element) {
            return element.getProgramVariable() == programVariable &&
                   element.isArrayIndex() == isArrayIndex &&
                   element.getArrayIndex() == arrayIndex &&
                   element.getCondition() == condition;
         }
      });
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

   /**
    * {@inheritDoc}
    */
   @Override
   public ISymbolicValue getValue(final IProgramVariable programVariable, 
                                  final boolean isArrayIndex, 
                                  final int arrayIndex,
                                  final Term condition) {
      return JavaUtil.search(values, new IFilter<ISymbolicValue>() {
         @Override
         public boolean select(ISymbolicValue element) {
            return element.getProgramVariable() == programVariable &&
                   element.isArrayIndex() == isArrayIndex &&
                   element.getArrayIndex() == arrayIndex &&
                   element.getCondition() == condition;
         }
      });
   }
}