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

/*******************************************************************************
 * Copyright (c) 2000, 2011 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.key_project.key4eclipse.resources.ui.wizard;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.wizard.Wizard;
import org.key_project.key4eclipse.common.ui.wizard.AbstractNewJavaProjectWizard;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * {@link Wizard} to create a new KeY project.
 * @author Martin Hentschel
 */
public class KeYProjectWizard extends AbstractNewJavaProjectWizard {
   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeWindowTitle() {
      return "New KeY Project";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeDescription() {
      return "Create a KeY project in the workspace or in an external location.";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeTitle() {
      return "Create a KeY Project";
   }
   
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
   @Override
   public boolean performFinish(){
      boolean done = super.performFinish();
      if (done) {
         IProject project = getCreatedElement().getJavaProject().getProject();
         try {
            IProjectDescription description = project.getDescription();
            String[] newNatures = ArrayUtil.insert(description.getNatureIds(), KeYProjectNature.NATURE_ID, 0);
            description.setNatureIds(newNatures);
            project.setDescription(description,null);
         }
         catch (CoreException e) {
            LogUtil.getLogger().createErrorStatus(e);
         }
      }
      return done;
   }
}