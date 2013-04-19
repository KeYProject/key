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

package org.key_project.util.eclipse;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.util.Collection;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.model.IWorkbenchAdapter;
import org.key_project.util.Activator;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

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
    * Returns the file name without file extension for the given {@link IFile}.
    * @param file The {@link IFile} for that the file name without extension is needed.
    * @return The file name without extension or {@code null} if it was not possible to compute it.
    */
   public static String getFileNameWithoutExtension(IFile file) {
      if (file != null) {
         return IOUtil.getFileNameWithoutExtension(file.getName());
      }
      else {
         return null;
      }
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

   /**
    * <p>
    * Copies the given {@link File}s into the specified {@link IContainer}.
    * </p>
    * <p>
    * <b>Attention: </b> Existing files will be overwritten!
    * </p>
    * @param target The {@link IContainer} to copy to.
    * @param opener An optional {@link IFileOpener} which can be used to modify the content of files during the copy process.
    * @param source The {@link File} to copy.
    * @throws CoreException Occurred Exception.
    */
   public static void copyIntoWorkspace(IContainer target, IFileOpener opener, Collection<File> source) throws CoreException {
      if (source != null) {
         copyIntoWorkspace(target, opener, source.toArray(new File[source.size()]));
      }
   }

   /**
    * <p>
    * Copies the given {@link File}s into the specified {@link IContainer}.
    * </p>
    * <p>
    * <b>Attention: </b> Existing files will be overwritten!
    * </p>
    * @param target The {@link IContainer} to copy to.
    * @param opener An optional {@link IFileOpener} which can be used to modify the content of files during the copy process.
    * @param source The {@link File} to copy.
    * @throws CoreException Occurred Exception.
    */
   public static void copyIntoWorkspace(IContainer target, IFileOpener opener, File... source) throws CoreException {
      try {
         if (source != null) {
            if (target == null) {
               throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Target not defined.", null));
            }
            if (!target.exists()) {
               throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Target \"" + target + "\" does not exist.", null));
            }
            if (opener == null) {
               opener = new DefaultFileOpener();
            }
            for (File file : source) {
               if (file != null) {
                  if (file.isFile()) {
                     IFile targetFile = target.getFile(new Path(file.getName()));
                     createFile(targetFile, opener.open(file), null);
                  }
                  else {
                     IFolder targetFolder = target.getFolder(new Path(file.getName()));
                     if (!targetFolder.exists()) {
                        targetFolder.create(true, true, null);
                     }
                     copyIntoWorkspace(targetFolder, opener, file.listFiles());
                  }
               }
            }
         }
      }
      catch (IOException e) {
         throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, e.getMessage(), e));
      }
   }
   
   /**
    * Instances of this class are used to open an {@link InputStream} of a {@link File}.
    * @author Martin Hentschel
    */
   public static interface IFileOpener {
      /**
       * Opens the {@link InputStream} for the given {@link File}.
       * @param file The {@link File} to open.
       * @return The {@link InputStream} for the given {@link File}.
       * @throws IOException Occurred Exception.
       */
      public InputStream open(File file) throws IOException;
   }
   
   /**
    * Default implementation of {@link IFileOpener}.
    * @author Martin Hentschel
    */
   public static class DefaultFileOpener implements IFileOpener {
      /**
       * {@inheritDoc}
       */
      @Override
      public InputStream open(File file) throws IOException {
         return new FileInputStream(file);
      }
   }

   /**
    * <p>
    * Creates the given {@link IFile} if not already present or changes
    * it contents otherwise.
    * </p>
    * <p>
    * <b>Attention: </b> Existing files will be overwritten!
    * </p>
    * @param file The {@link IFile} to create or to change its content.
    * @param in The {@link InputStream} which provides the new content.
    * @param monitor An optional {@link IProgressMonitor} to use.
    * @throws CoreException Occurred Exception.
    */
   public static void createFile(IFile file, InputStream in, IProgressMonitor monitor) throws CoreException {
      try {
         if (file != null) {
            if (in == null) {
               in = new ByteArrayInputStream(new byte[0]);
            }
            if (file.exists()) {
               file.setContents(in, true, true, monitor);
            }
            else {
               file.create(in, true, monitor);
            }
         }
      }
      finally {
         try {
            if (in != null) {
               in.close();
            }
         }
         catch (IOException e) {
            throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, e.getMessage(), e));
         }
      }
   }
   
   /**
    * Reads the complete content from the {@link IFile}.
    * @param file The {@link IFile} to read from.
    * @return The read content or {@code null} if the {@link IFile} is {@code null} or don't exist.
    * @throws CoreException Occurred Exception.
    */
   public static String readFrom(IFile file) throws CoreException {
      try {
         if (file != null && file.exists()) {
            InputStream content = file.getContents();
            return IOUtil.readFrom(content);
         }
         else {
            return null;
         }
      }
      catch (IOException e) {
         throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, e.getMessage(), e));
      }
   }
}