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

package org.key_project.sed.key.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.debug.core.DebugException;
import org.key_project.sed.key.ui.util.LogUtil;
import org.key_project.sed.key.ui.visualization.execution_tree.command.VisualizeMemoryLayoutsCommand;

/**
 * This {@link PropertyTester} can be used to check if memory layouts can
 * be visualized for the given {@link Object}. The check is delegated to
 * {@link VisualizeMemoryLayoutsCommand#canVisualize(Object)}.
 * @author Martin Hentschel
 */
public class CanVisualizeMemoryLayoutsPropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      try {
         return VisualizeMemoryLayoutsCommand.canVisualize(receiver);
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }
}