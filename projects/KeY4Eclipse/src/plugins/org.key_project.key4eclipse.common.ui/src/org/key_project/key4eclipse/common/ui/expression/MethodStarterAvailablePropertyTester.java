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

package org.key_project.key4eclipse.common.ui.expression;

import java.util.Iterator;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.internal.ui.actions.SelectionConverter;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.ui.IEditorPart;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * A {@link PropertyTester} which checks if the global start functionality
 * via {@link IMethodStarter}s is available or not.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class MethodStarterAvailablePropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      if (StarterUtil.areMethodStartersAvailable()) {
         boolean inSourcePath = isInSourcePath(receiver);
         if (receiver instanceof Object[]) {
            Object[] array = (Object[]) receiver;
            int i = 0;
            while (!inSourcePath && i < array.length) {
               if (isInSourcePath(array[i])) {
                  inSourcePath = true;
               }
               i++;
            }
         }
         else if (receiver instanceof Iterable<?>) {
            Iterator<?> iter = ((Iterable<?>) receiver).iterator();
            while (!inSourcePath && iter.hasNext()) {
               if (isInSourcePath(iter.next())) {
                  inSourcePath = true;
               }
            }
         }
         return inSourcePath;
      }
      else {
         return false;
      }
   }

   /**
    * Checks if the given {@link Object} is part of the specified source path.
    * @param receiver The {@link Object} to check.
    * @return {@code true} is part of source path, {@code false} is not part of source path or unknown.
    */
   protected boolean isInSourcePath(Object receiver) {
      try {
         IResource resource = null;
         if (receiver instanceof IResource) {
            resource = (IResource) receiver;
         }
         else if (receiver instanceof IAdaptable) {
            resource = (IResource) ((IAdaptable) receiver).getAdapter(IResource.class);
         }
         else if (receiver instanceof ITextSelection) {
            IEditorPart editor = WorkbenchUtil.getActiveEditor();
            if (editor instanceof JavaEditor) {
               JavaEditor javaEditor = (JavaEditor) editor;
               IJavaElement element = SelectionConverter.resolveEnclosingElement(javaEditor, (ITextSelection) receiver);
               if (element != null) {
                  resource = element.getResource();
               }
            }
         }
         if (resource != null) {
            IProject project = resource.getProject();
            IResource sourceLocation = KeYResourceProperties.getSourceClassPathResource(project);
            return sourceLocation != null && sourceLocation.contains(resource);
         }
         else {
            return false;
         }
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }
}