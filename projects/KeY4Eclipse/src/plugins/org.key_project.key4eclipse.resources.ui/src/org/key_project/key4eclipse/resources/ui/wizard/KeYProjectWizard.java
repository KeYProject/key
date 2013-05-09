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
import org.key_project.key4eclipse.resources.ui.util.LogUtil;
import org.key_project.util.java.ObjectUtil;


@SuppressWarnings("restriction")
public class KeYProjectWizard extends JavaProjectWizard{

   public KeYProjectWizard(){
      super();
      this.setWindowTitle("New KeY Project");
   }
   
   @Override
   public void addPages(){
      super.addPages();
      try {
         Object obj = ObjectUtil.get(this, "fFirstPage");
         if(obj instanceof WizardPage){
            ((WizardPage)obj).setTitle("Create a KeY Project");
         }
         else{
            LogUtil.getLogger().logWarning("API has changed");
         }
      }
      catch (SecurityException e) {
         // TODO Auto-generated catch block
         LogUtil.getLogger().logError(e);
      }
      catch (NoSuchFieldException e) {
         // TODO Auto-generated catch block
         LogUtil.getLogger().logError(e);
      }
      catch (IllegalArgumentException e) {
         // TODO Auto-generated catch block
         LogUtil.getLogger().logError(e);
      }
      catch (IllegalAccessException e) {
         // TODO Auto-generated catch block
         LogUtil.getLogger().logError(e);
      }
      
   }
   
   @Override
   public boolean performFinish(){
      boolean res = super.performFinish();
      if(res){
         final IProject project = getCreatedElement().getJavaProject().getProject();
         try {
            IProjectDescription description = project.getDescription();
            String[] natures = description.getNatureIds();
            String[] newNatures = new String[natures.length + 1];
            System.arraycopy(natures,0,newNatures,0,natures.length);
            newNatures[natures.length] = "org.key_project.key4eclipse.resources.KeYProjectNature";
            description.setNatureIds(newNatures);
            project.setDescription(description,null);
         }
         catch (CoreException e) {
            LogUtil.getLogger().createErrorStatus(e);
         }
      }
      return res;
   }
}