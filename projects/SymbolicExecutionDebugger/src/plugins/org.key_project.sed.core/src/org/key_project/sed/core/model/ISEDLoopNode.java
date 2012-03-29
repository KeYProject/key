package org.key_project.sed.core.model;

import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.impl.AbstractSEDLoopNode;
import org.key_project.sed.core.model.memory.SEDMemoryLoopNode;

/**
 * A node in the symbolic execution tree which represents a loop.
 * e.g. {@code while(x >= 0)}. The loop condition ({@code x >= 0}) itself 
 * is represented as {@link ISEDLoopCondition} node.
 * <p>
 * A symbolic loop node is also a normal stack frame ({@link IStackFrame})
 * for compatibility reasons with the Eclipse debug API.
 * </p>
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDLoopNode} instead of implementing this
 * interface directly. {@link SEDMemoryLoopNode} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDLoopNode extends ISEDDebugNode, IStackFrame {

}
