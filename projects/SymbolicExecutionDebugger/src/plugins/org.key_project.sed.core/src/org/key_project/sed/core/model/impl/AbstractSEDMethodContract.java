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

import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.ISEDMethodContract;

/**
 * Provides a basic implementation of {@link ISEDMethodContract}.
 * @author Martin Hentschel
 * @see ISEDBranchCondition
 */
public abstract class AbstractSEDMethodContract extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDMethodContract {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this method contract is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    */
   public AbstractSEDMethodContract(ISEDDebugTarget target, 
                                    ISEDDebugNode parent,
                                    ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      String kind = "Method Contract";
      if (isPreconditionComplied()) {
         if (!hasNotNullCheck() || isNotNullCheckComplied()) {
            return kind;
         }
         else {
            return kind + " (Null Pointer Check failed)";
         }
      }
      else {
         if (!hasNotNullCheck() || isNotNullCheckComplied()) {
            return kind + " (Precondition Check failed)";
         }
         else {
            return kind + " (Precondition Check and Null Pointer Check failed)";
         }
      }
   }
}