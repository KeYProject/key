/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

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