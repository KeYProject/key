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

package de.hentschel.visualdbc.datasource.ui.setting;

import java.io.File;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IJavaElement;


/**
 * Special implementation of {@link JavaPackageSettingControl} that returns
 * as value the local {@link File} instance or the {@link IPath} to a
 * workspace resource. It autoamtically converts {@link IJavaElement} into
 * the workspace resource {@link IPath}. 
 * @author Martin Hentschel
 */
public class FileOrResourceJavaPackageSettingControl extends JavaPackageSettingControl {
   /**
    * Returns the specific value from the super class.
    * @return The specific value.
    */
   public Object getSpecificValue() {
      return super.getValue();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getValue() {
      Object specificValue = getSpecificValue();
      Object result = null;
      if (specificValue instanceof File) {
         result = specificValue;
      }
      else if (specificValue instanceof IPath) {
         result = specificValue;
      }
      else if (specificValue instanceof IJavaElement) {
         IResource resource = ((IJavaElement)specificValue).getResource();
         result = resource.getFullPath(); 
      }
      else if (specificValue != null){
         Assert.isTrue(false, "Unknown specific value: " + specificValue);
      }
      return result;
   }
  
   /**
    * {@inheritDoc}
    */
   @Override
   public String getValidationMessage() {
      String message = getValidationMessage(getSpecificValue());
      if (message == null) {
         Object fileValue = getValue();
         if (fileValue == null) {
            message = "Can't find local directory or workspace resource.";
         }
      }
      return message;
   }
}