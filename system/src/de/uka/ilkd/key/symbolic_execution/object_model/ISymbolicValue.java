// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicValue;

/**
 * <p>
 * Represents a variable of an {@link ISymbolicState} or {@link ISymbolicObject}
 * which contains a value of a primitive type.
 * </p>
 * <p>
 * The default implementation is {@link SymbolicValue}.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicValue
 */
public interface ISymbolicValue extends ISymbolicElement {
   /**
    * Returns a human readable name.
    * @return A human readable name.
    */
   public String getName();
   
   /**
    * Checks if an array index or a program variable is represented.
    * @return {@code true} array index, {@code false} program variable.
    */
   public boolean isArrayIndex();
   
   /**
    * Returns the represented array index or {@code -1} if a program variable is represented..
    * @return The represented array index or {@code -1} if a program variable is represented..
    */
   public int getArrayIndex();
   
   /**
    * Returns the represented {@link IProgramVariable} or {@code null} if an array index is represented.
    * @return The represented {@link IProgramVariable} or {@code null} if an array index is represented.
    */
   public IProgramVariable getProgramVariable();
   
   /**
    * Returns the represented {@link IProgramVariable} as human readable {@link String} or {@code null} if an array index is represented.
    * @return The represented {@link IProgramVariable} as human readable {@link String} or {@code null} if an array index is represented.
    */
   public String getProgramVariableString();
   
   /**
    * Returns the value of the represented variable.
    * @return The value of the represented variable.
    */
   public Term getValue();
   
   /**
    * Returns the value of the represented variable as human readable {@link String}.
    * @return The value of the represented variable as human readable {@link String}.
    */
   public String getValueString();
   
   /**
    * Returns the type of the value.
    * @return The type of the value.
    */
   public Sort getType();
   
   /**
    * Returns the type of the value as human readable string.
    * @return The type of the value as human readable string.
    */
   public String getTypeString();
   
   /**
    * <p>
    * Returns the optional condition under which this value is valid.
    * </p>
    * <p>
    * The condition should be {@code null} by default. Only in rare cases,
    * e.g. path condition is not strong enough to describe the path completely, 
    * is a condition is provided.
    * </p>
    * @return The optional condition under which this value is valid.
    */
   public Term getCondition();
   
   /**
    * <p>
    * Returns the optional condition under which this value is valid as human readable {@link String}.
    * </p>
    * <p>
    * The condition should be {@code null} by default. Only in rare cases,
    * e.g. path condition is not strong enough to describe the path completely, 
    * is a condition is provided.
    * </p>
    * @return The optional condition under which this value is valid as human readable {@link String}.
    */
   public String getConditionString();
}