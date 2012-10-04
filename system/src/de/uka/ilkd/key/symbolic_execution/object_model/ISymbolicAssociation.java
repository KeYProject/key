package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicAssociation;

/**
 * <p>
 * Represents an association of an {@link ISymbolicState} or {@link ISymbolicObject}
 * which is a reference to an {@link ISymbolicObject}.
 * </p>
 * <p>
 * The default implementation is {@link SymbolicAssociation}.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicAssociation
 */
public interface ISymbolicAssociation {
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
    * Returns the target {@link ISymbolicObject}.
    * @return The target {@link ISymbolicObject}.
    */
   public ISymbolicObject getTarget();
}