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

package org.key_project.sed.key.core.launch;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.sourcelookup.AbstractSourceLookupParticipant;
import org.key_project.sed.core.model.ISourcePathProvider;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

/**
 * {@link AbstractSourceLookupParticipant} implementation for the
 * Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
public class KeYSourceLookupParticipant extends AbstractSourceLookupParticipant {
   /**
    * {@inheritDoc}
    */
   public String getSourceName(Object object) throws CoreException {
      if (object instanceof IAdaptable) {
         IAdaptable adaptable = (IAdaptable)object;
         List<File> locations = listAllSourceLocations(adaptable);
         ISourcePathProvider provider = (ISourcePathProvider)adaptable.getAdapter(ISourcePathProvider.class);
         String path = provider.getSourcePath();
         String bestPrefix = findPrefix(locations, path);
         if (bestPrefix != null) {
            return path.substring(bestPrefix.length());
         }
         else {
            return path;
         }
      }
      else {
         return null;
      }
   }

   /**
    * Lists all used source locations defined by the {@link KeYLaunchSettings}.
    * @param adaptable The object which provides the {@link KeYLaunchSettings}.
    * @return All used source locations.
    */
   protected List<File> listAllSourceLocations(IAdaptable adaptable) {
      List<File> result = new LinkedList<File>();
      if (adaptable instanceof IDebugElement) {
         IDebugTarget target = ((IDebugElement) adaptable).getDebugTarget();
         if (target instanceof KeYDebugTarget) {
            KeYLaunchSettings settings = ((KeYDebugTarget) target).getLaunchSettings();
            File location = settings.getLocation();
            if (location != null) {
               result.add(location);
            }
            List<File> classPaths = settings.getClassPaths();
            if (classPaths != null) {
               result.addAll(classPaths);
            }
            File bootClassPath = settings.getBootClassPath();
            if (bootClassPath != null) {
               result.add(bootClassPath);
            }
         }
      }
      return result;
   }
   
   /**
    * Selects a prefix of the given path.
    * @param locations The possible prefixes.
    * @param path The path for which the prefix is required.
    * @return The prefix or {@code null} if no prefix is available.
    */
   protected String findPrefix(List<File> locations, final String path) {
      if (path != null) {
         File prefixFile = CollectionUtil.search(locations, new IFilter<File>() {
            @Override
            public boolean select(File element) {
               return path.startsWith(element.toString());
            }
         });
         return prefixFile != null ? prefixFile.toString() : null;
      }
      else {
         return null;
      }
   }
}