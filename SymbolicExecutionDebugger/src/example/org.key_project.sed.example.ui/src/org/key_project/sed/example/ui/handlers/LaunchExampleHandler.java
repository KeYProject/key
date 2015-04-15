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

package org.key_project.sed.example.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.CoreException;
import org.key_project.sed.example.ui.util.ExampleLaunchUtil;

/**
 * An {@link AbstractHandler} which launches the example symbolic execution 
 * engine with help of the {@link ExampleLaunchUtil}.
 * <p>
 * May use the extension point {@code org.eclipse.debug.ui.launchShortcuts}
 * to add your own launch shortcut to context menus.
 */
public class LaunchExampleHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
	   try {
         ExampleLaunchUtil.launch();
         return null;
      }
      catch (CoreException e) {
         throw new ExecutionException(e.getMessage(), e);
      }
	}
}
