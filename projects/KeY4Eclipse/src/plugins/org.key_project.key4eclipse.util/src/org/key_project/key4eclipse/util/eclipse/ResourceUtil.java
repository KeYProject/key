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

package org.key_project.key4eclipse.util.eclipse;

import java.io.File;
import java.net.URI;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.model.IWorkbenchAdapter;
import org.key_project.key4eclipse.util.java.StringUtil;

/**
 * Provides static methods to work with workspace resources.
 * @author Martin Hentschel
 */
public class ResourceUtil {
   /**
    * Forbid instances by this private constructor.
    */
   private ResourceUtil() {
   }
   
   /**
    * Returns all workspace {@link IResource}s that represents the given
    * {@link File} in the local file system.
    * @param location The file or folder in the local file system.
    * @return The found workspace {@link IResource}s.
    */
   public static IResource[] findResourceForLocation(File location) {
      if (location != null) {
         URI uri = location.toURI();
         if (location.isFile()) {
            return ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(uri);
         }
         else {
            return ResourcesPlugin.getWorkspace().getRoot().findContainersForLocationURI(uri);
         }
      }
      else {
         return new IContainer[0];
      }
   }
   
   /**
    * Returns the local location on the hard discs for the {@link IResource}.
    * @param resource The {@link IResource}.
    * @return The local location for the {@link IResource} or {@code null} if the {@link IResource} is {@code null} or if the {@link IResource} is not local.
    */
   public static File getLocation(IResource resource) {
      File location = null;
      if (resource != null && resource.getLocationURI() != null) {
         location = new File(resource.getLocationURI());
      }
      return location;
   }

   /**
    * <p>
    * Returns the {@link Image} for the given {@link IResource}.
    * </p>
    * <p>
    * <b>Attention: </b> The caller is responsible to dispose the created {@link Image}!
    * </p>
    * @param resource The {@link IResource} for that an {@link Image} is needed.
    * @return The found {@link Image} or {@code null} if no one can be found.
    */
   public static Image getImage(IResource resource) {
      if (resource != null) {
          IWorkbenchAdapter adapter = (IWorkbenchAdapter)resource.getAdapter(IWorkbenchAdapter.class);
          ImageDescriptor id = adapter.getImageDescriptor(resource);
          return id.createImage();
      }
      else {
         return null;
      }
   }

   /**
    * Returns the {@link IProject} for the given name. If no project with
    * the name an {@link IProject} reference is returned, 
    * but {@link IProject#exists()} is still {@code false}.
    * @param projectName The name of the project.
    * @return The found {@link IProject} or {@code null} if the project name is {@code null}/empty.
    */
   public static IProject getProject(String projectName) {
      if (!StringUtil.isTrimmedEmpty(projectName)) {
         return ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
      }
      else {
         return null;
      }
   }
}
