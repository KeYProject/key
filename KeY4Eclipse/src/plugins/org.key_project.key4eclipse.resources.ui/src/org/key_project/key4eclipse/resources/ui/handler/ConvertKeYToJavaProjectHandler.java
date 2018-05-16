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

package org.key_project.key4eclipse.resources.ui.handler;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.*;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuilder;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;

public class ConvertKeYToJavaProjectHandler extends AbstractSaveExecutionHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      Object[] elements = SWTUtil.toArray(selection);
      for(Object obj : elements) {
         IProject project = null;
         if (obj instanceof IJavaProject) {
            obj = ((IJavaProject) obj).getProject();
         }
         if (obj instanceof IProject && KeYResourcesUtil.isKeYProject((IProject) obj)) {
            project = (IProject) obj;
            IProjectDescription description = project.getDescription();
            String[] newNatures = ArrayUtil.remove(description.getNatureIds(), KeYProjectNature.NATURE_ID);
            description.setNatureIds(newNatures);
            
            final ICommand[] builders = description.getBuildSpec();
            ICommand[] newBuilders = builders;
            for (ICommand cmd : builders) {
                if (cmd.getBuilderName().equals(KeYProjectBuilder.BUILDER_ID)) {
                    newBuilders = ArrayUtil.remove(builders, cmd);                    
                }
            }
            description.setBuildSpec(newBuilders);
            project.setDescription(description, null);   
            project.deleteMarkers(null, true, IResource.DEPTH_INFINITE);
            project.refreshLocal(IResource.DEPTH_INFINITE, null);
            KeYResourcesUtil.synchronizeProject(project);
         }
      }
      return null;
   }
}