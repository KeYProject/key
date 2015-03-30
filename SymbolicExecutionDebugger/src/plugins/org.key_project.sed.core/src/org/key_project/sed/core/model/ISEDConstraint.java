package org.key_project.sed.core.model;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.impl.AbstractSEDConstraint;
import org.key_project.sed.core.model.memory.SEDMemoryConstraint;

/**
 * A constraint which is considered during symbolic execution.
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDConstraint} instead of implementing this
 * interface directly. {@link SEDMemoryConstraint} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 */
public interface ISEDConstraint extends ISEDDebugElement {
   /**
    * Returns the human readable constraint name.
    * @return The human readable constraint name.
    * @throws DebugException Occurred Exception.
    */
   public String getName() throws DebugException;
}
