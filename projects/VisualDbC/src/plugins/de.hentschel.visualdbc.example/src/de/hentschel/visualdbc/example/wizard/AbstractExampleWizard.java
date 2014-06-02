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

package de.hentschel.visualdbc.example.wizard;

import java.io.IOException;
import java.util.Collections;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.key_project.key4eclipse.common.ui.wizard.AbstractNewJavaProjectWizard;

import de.hentschel.visualdbc.datasource.key.model.KeyDriver;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcProperty;

/**
 * Provides a basic functionality for example wizards that are based on 
 * java projects.
 * @author Martin Hentschel
 */
public abstract class AbstractExampleWizard extends AbstractNewJavaProjectWizard {
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