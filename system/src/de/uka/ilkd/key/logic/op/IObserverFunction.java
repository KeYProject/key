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

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;

public interface IObserverFunction extends SortedOperator {

   /**
    * Returns the result type of this symbol.
    */
   public abstract KeYJavaType getType();

   /**
    * Returns the container type of this symbol; for non-static observer 
    * symbols, this corresponds to the sort of its second argument.
    */
   public abstract KeYJavaType getContainerType();

   /**
    * Tells whether the observer symbol is static.
    */
   public abstract boolean isStatic();

   /**
    * Check the state count of the declaration (no_state = 0, two_state = 2, 1 otherwise).
    */
   public abstract int getStateCount();

   /**
    * Check the heap count of the declaration, e.g. the base heap and extra heap.
    */
   public abstract int getHeapCount(Services services);   
   
   /**
    * Gives the number of parameters of the observer symbol. "Parameters" here
    * includes only the *explicit* parameters, not the heap and the receiver
    * object. Thus, for observer symbols representing model fields, this will
    * always return 0.
    */
   public abstract int getNumParams();

   /**
    * Gives the type of the i-th parameter of this observer symbol. 
    * "Parameters" here includes only the *explicit* parameters, not the heap 
    * and the receiver object. 
    */
   public abstract KeYJavaType getParamType(int i);

   /**
    * Returns the parameter types of this observer symbol. "Parameters" here
    * includes only the *explicit* parameters, not the heap and the receiver
    * object. 
    */
   public abstract ImmutableArray<KeYJavaType> getParamTypes();

}