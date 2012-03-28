package org.key_project.sed.core.model;

import org.eclipse.debug.core.model.ITerminate;
import org.key_project.sed.core.model.impl.AbstractSEDBranchCondition;
import org.key_project.sed.core.model.memory.SEDMemoryBranchCondition;

/**
 * A node in the symbolic execution tree which represents a branch condition,
 * e.g. {@code x < 0}.
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDBranchCondition} instead of implementing this
 * interface directly. {@link SEDMemoryBranchCondition} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDBranchCondition extends ISEDDebugNode, ITerminate {

}
