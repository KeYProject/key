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

package org.key_project.key4eclipse.common.ui.wizard;

import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.wizards.JavaProjectWizard;
import org.eclipse.jface.wizard.WizardPage;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * Provides a basic functionality for new wizards that are based on 
 * Java Projects.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public abstract class AbstractNewJavaProjectWizard extends JavaProjectWizard {
   /**
    * Constructor.
    */
   public AbstractNewJavaProjectWizard() {
      setWindowTitle(computeWindowTitle());
   }
   
   /**
    * Computes the window title.
    * @return The window title to set.
    */
   protected abstract String computeWindowTitle();
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages(){
      super.addPages();
      try {
         Object obj = ObjectUtil.get(this, "fFirstPage");
         if(obj instanceof WizardPage) {
            WizardPage page = (WizardPage) obj;
            page.setTitle(computeTitle());
            page.setDescription(computeDescription());
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
    * Computes the description.
    * @return The description to set.
    */
   protected abstract String computeDescription();
   
   /**
    * Computes the title.
    * @return The title to set.
    */
   protected abstract String computeTitle();

   /**
    * Returns the {@link IResource} that will contain java source code.
    * @return The found {@link IResource} with java source code or {@code null} if no one was found. 
    * @throws JavaModelException Occurred Exception.
    */
   protected IResource getSourceDirectory() throws JavaModelException {
      IResource sourceDirectory = null;
      IJavaElement newElement = getCreatedElement();
      if (newElement != null) {
         IPackageFragmentRoot[] roots = newElement.getJavaProject().getPackageFragmentRoots();
         int i = 0;
         while (sourceDirectory == null && i < roots.length) {
            if (roots[i].getResource() != null) {
               sourceDirectory = roots[i].getResource();
            }
         }
      }
      return sourceDirectory;
   }
}