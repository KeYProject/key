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
import org.eclipse.jdt.internal.ui.wizards.JavaProjectWizard;
import org.eclipse.jface.wizard.WizardPage;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;


@SuppressWarnings("restriction")
public class KeYProjectWizard extends JavaProjectWizard {
   
   /**
    * The Constructor that sets the Window Title of the Wizard to "New KeYProject"
    */
   public KeYProjectWizard(){
      super();
      this.setWindowTitle("New KeY Project");
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages(){
      super.addPages();
      try {
         Object obj = ObjectUtil.get(this, "fFirstPage");
         if(obj instanceof WizardPage) {
            ((WizardPage)obj).setTitle("Create a KeY Project");
         }
         else {
            LogUtil.getLogger().logWarning("API has changed");
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
      }
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish(){
      boolean result = super.performFinish();
      if (result) {
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
      return result;
   }
}