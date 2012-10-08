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
public interface ISymbolicValue {
   /**
    * Returns the represented {@link IProgramVariable}.
    * @return The represented {@link IProgramVariable}.
    */
   public IProgramVariable getProgramVariable();
   
   /**
    * Returns the represented {@link IProgramVariable} as human readable {@link String}.
    * @return The represented {@link IProgramVariable} as human readable {@link String}.
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
}