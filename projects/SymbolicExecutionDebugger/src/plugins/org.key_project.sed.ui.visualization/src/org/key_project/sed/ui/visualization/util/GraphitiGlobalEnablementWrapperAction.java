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

package org.key_project.sed.ui.visualization.util;

import org.eclipse.gef.ui.actions.UpdateAction;
import org.eclipse.jface.action.IAction;
import org.key_project.util.eclipse.view.editorInView.GlobalEnablementWrapperAction;

public class GraphitiGlobalEnablementWrapperAction extends GlobalEnablementWrapperAction implements UpdateAction {

   public GraphitiGlobalEnablementWrapperAction(IAction action) {
      super(action);
   }

   @Override
   public void update() {
      if (getAction() instanceof UpdateAction) {
         ((UpdateAction)getAction()).update();
      }
   }
}