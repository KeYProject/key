package org.key_project.sed.core.model;

import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.model.impl.AbstractSEDVariable;

/**
 * A variable of a node in the symbolic execution tree,
 * e.g. the method call parameter {@code int a}.
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDVariable} instead of implementing this
 * interface directly. {@link SEDMemoryVariable} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 */
public interface ISEDVariable extends IVariable, ISEDDebugElement {
}
