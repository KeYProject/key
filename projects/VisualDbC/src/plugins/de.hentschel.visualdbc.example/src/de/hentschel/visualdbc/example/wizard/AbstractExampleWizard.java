/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.example.wizard;

import java.io.IOException;
import java.util.Collections;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.wizards.JavaProjectWizard;
import org.eclipse.jdt.internal.ui.wizards.NewWizardMessages;

import de.hentschel.visualdbc.datasource.key.model.KeyDriver;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcProperty;
import de.hentschel.visualdbc.example.util.LogUtil;

/**
 * Provides a basic functionality for example wizards that are based on 
 * java projects.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public abstract class AbstractExampleWizard extends JavaProjectWizard {
   /**
    * Constructor.
    */
   public AbstractExampleWizard() {
      setWindowTitle(NewWizardMessages.JavaProjectWizard_title + " with content from " + getExampleName());
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

   /**
    * Updates the location in the model file.
    * @param modelFile The model file to update.
    * @param locationFolder The location folder to set.
    * @throws IOException Occurred Exception
    */
   protected void updateLocationInModelFile(IFile modelFile, IFolder locationFolder) throws IOException {
      if (modelFile != null && modelFile.exists()) {
         ResourceSet rst = new ResourceSetImpl();
         Resource resource = rst.getResource(URI.createPlatformResourceURI(modelFile.getFullPath().toString(), true), true);
         if (resource.getContents().size() >= 1 && resource.getContents().get(0) instanceof DbcModel) {
            DbcModel model = (DbcModel)resource.getContents().get(0);
            for (DbcProperty property : model.getConnectionSettings()) {
               if (KeyDriver.SETTING_LOCATION.equals(property.getKey())) {
                  property.setValue(locationFolder.getFullPath().toString());
               }
            }
         }
         resource.save(Collections.EMPTY_MAP);
         resource.unload();
      }
   }
}
