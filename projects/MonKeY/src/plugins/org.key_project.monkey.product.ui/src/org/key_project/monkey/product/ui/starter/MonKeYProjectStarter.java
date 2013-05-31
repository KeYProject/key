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

package org.key_project.monkey.product.ui.starter;

import org.eclipse.core.resources.IProject;
import org.eclipse.ui.IViewPart;
import org.key_project.key4eclipse.common.ui.starter.IProjectStarter;
import org.key_project.monkey.product.ui.perspective.MonKeYPerspective;
import org.key_project.monkey.product.ui.view.MonKeYView;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Starts MonKeY which means that the MonKeY perspective is opened
 * and loads the project in it.
 * @author Martin Hentschel
 */
public class MonKeYProjectStarter implements IProjectStarter {
   /**
    * {@inheritDoc}
    */
   @Override
   public void open(IProject project) throws Exception {
      WorkbenchUtil.openPerspective(MonKeYPerspective.ID);
      IViewPart monkeyView = WorkbenchUtil.findView(MonKeYView.ID);
      if (monkeyView == null) {
         monkeyView = WorkbenchUtil.openView(MonKeYView.ID);
      }
      if (monkeyView instanceof MonKeYView) {
         ((MonKeYView)monkeyView).loadProject(project);
      }
   }
}