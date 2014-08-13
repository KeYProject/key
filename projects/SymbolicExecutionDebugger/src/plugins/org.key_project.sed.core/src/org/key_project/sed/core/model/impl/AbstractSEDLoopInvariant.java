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

package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDLoopInvariant;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDLoopInvariant}.
 * @author Martin Hentschel
 * @see ISEDBranchCondition
 */
public abstract class AbstractSEDLoopInvariant extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDLoopInvariant {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this loop invariant is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    */
   public AbstractSEDLoopInvariant(ISEDDebugTarget target, 
                                   ISEDDebugNode parent,
                                   ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      String kind = "Loop Invariant";
      if (isInitiallyValid()) {
         return kind;
      }
      else {
         return kind + " (Initially invalid)";
      }
   }
}