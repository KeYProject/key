package org.key_project.sed.core.model;

import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IThread;
import org.key_project.sed.core.model.impl.AbstractSEDThread;
import org.key_project.sed.core.model.memory.SEDMemoryThread;

/**
 * A thread is the root of the symbolic execution tree.
 * <p>
 * A symbolic thread is also a normal thread ({@link IThread})
 * for compatibility reasons with the Eclipse debug API. But the default
 * provided {@link IStackFrame}s are not used anymore. Instead the contained
 * {@link ISEDDebugNode}s are used.
 * </p>
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDThread} instead of implementing this
 * interface directly. {@link SEDMemoryThread} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDThread extends ISEDDebugNode, IThread {
}
