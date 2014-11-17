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

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.internal.ui.wizards.NewWizardMessages;
import org.eclipse.jdt.ui.wizards.NewJavaProjectWizardPageOne;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.swt.widgets.Display;
import org.key_project.key4eclipse.common.ui.util.LogUtil;

/**
 * Provides a basic functionality for new wizards that are based on 
 * Java Projects.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public abstract class AbstractNewJavaExampleProjectWizard extends AbstractNewJavaProjectWizard {
   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeWindowTitle() {
      return NewWizardMessages.JavaProjectWizard_title + " with content from " + getExampleName();
   }
   
   /**
    * Returns the example name.
    * @return The name of the example.
    */
   protected abstract String getExampleName();
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeDescription() {
      return NewWizardMessages.NewJavaProjectWizardPageOne_page_description + " It will be filled with content from " + getExampleName() + ".";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeTitle() {
      return NewWizardMessages.NewJavaProjectWizardPageOne_page_title + " with content from " + getExampleName();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      super.addPages();
      // Set initial project name.
      if (shouldSetInitialProjectName()) {
         for (IWizardPage page : getPages()) {
            if (page instanceof NewJavaProjectWizardPageOne) {
               final NewJavaProjectWizardPageOne one = (NewJavaProjectWizardPageOne)page;
               Display.getDefault().asyncExec(new Runnable() {
                  @Override
                  public void run() {
                     one.setProjectName(getExampleName());
                  }
               });
            }
         }
      }
   }
   
   /**
    * Checks if the initial project name should be set.
    * @return {@code true} set initial project name, {@code false} do not set initial project name.
    */
   protected boolean shouldSetInitialProjectName() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         // Create java project
         boolean done = super.performFinish();
         // Check if the project was created
         if (done) {
            // Get source code directory
            IResource sourceDirectory = getSourceDirectory();
            // Check if a source code directory was found
            if (sourceDirectory instanceof IContainer) {
               done = createExampleContent((IContainer)sourceDirectory);
            }
         }
         return done;
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }

   /**
    * Adds the example content to the given source directory.
    * @param sourceDirectory The given source directory.
    * @return {@code true} = close wizard, {@code false} = keep wizard opened.
    * @throws Exception Occurred Exception.
    */
   protected abstract boolean createExampleContent(IContainer sourceDirectory) throws Exception;
}