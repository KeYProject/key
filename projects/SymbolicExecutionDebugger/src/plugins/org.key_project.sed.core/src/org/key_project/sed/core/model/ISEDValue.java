package org.key_project.sed.core.model;

import org.eclipse.debug.core.model.IValue;
import org.key_project.sed.core.model.impl.AbstractSEDValue;

/**
 * A value of a variable of a node in the symbolic execution tree,
 * e.g. the method call parameter {@code int a} which has value {@code 42}.
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDValue} instead of implementing this
 * interface directly. {@link SEDMemoryValue} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 */
public interface ISEDValue extends IValue, ISEDDebugElement {

}
