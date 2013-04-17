/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDLoopNode;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDLoopNode}.
 * @author Martin Hentschel
 * @see ISEDLoopNode
 */
public abstract class AbstractSEDLoopNode extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDLoopNode {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this loop node is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this loop node is contained.
    */
   public AbstractSEDLoopNode(ISEDDebugTarget target, 
                                ISEDDebugNode parent,
                                ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      return "Loop Node";
   }
}