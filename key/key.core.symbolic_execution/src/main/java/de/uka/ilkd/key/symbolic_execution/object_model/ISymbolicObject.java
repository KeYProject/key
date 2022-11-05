package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicObject;

/**
 * <p>
 * Represents a symbolic object in an {@link ISymbolicLayout}.
 * </p>
 * <p>
 * The default implementation is {@link SymbolicObject}.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicObject
 */
public interface ISymbolicObject extends ISymbolicAssociationValueContainer {
    /**
     * Returns the name of this object.
     *
     * @return The name of this object.
     */
    public Term getName();

    /**
     * Returns the name of this object as human readable {@link String}.
     *
     * @return The name of this object as human readable {@link String}.
     */
    public String getNameString();

    /**
     * Returns the type of this object.
     *
     * @return The type of this object.
     */
    public Sort getType();

    /**
     * Returns the type of this object as human readable string.
     *
     * @return The type of this object as human readable string.
     */
    public String getTypeString();
}
