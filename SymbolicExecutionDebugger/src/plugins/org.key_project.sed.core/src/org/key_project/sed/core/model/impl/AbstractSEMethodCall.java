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

import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEThread;

/**
 * Provides a basic implementation of {@link ISEMethodCall}.
 * @author Martin Hentschel
 * @see ISEMethodCall
 */
public abstract class AbstractSEMethodCall extends AbstractSEGroupableStackFrameCompatibleDebugNode implements ISEMethodCall {
   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} in that this method call is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEThread} in that this method call is contained.
    */
   public AbstractSEMethodCall(ISEDebugTarget target, 
                                ISENode parent,
                                ISEThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      return "Method Call";
   }
}