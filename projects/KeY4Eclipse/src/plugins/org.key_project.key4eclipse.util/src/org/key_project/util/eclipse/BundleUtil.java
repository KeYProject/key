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

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.net.URLConnection;
import java.util.Enumeration;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.key_project.util.Activator;
import org.osgi.framework.Bundle;

/**
 * Provides static methods to work with {@link Bundle}s.
 * @author Martin Hentschel
 */
public final class BundleUtil {
   /**
    * Forbid instances by this private constructor.
    */
   private BundleUtil() {
   }

   /**
    * Extracts the specified files from the bundle into the target directory.
    * @param pluginId The ID of the plug-in that contains the data to extract.
    * @param pathInBundle The path in the bundle to extract.
    * @param target The target directory in the local file system.
    * @throws CoreException Occurred Exception.
    */
   public static void extractFromBundleToFilesystem(String pluginId, String pathInBundle, File target) throws CoreException {
       // Make sure that all parameters are defined.
       if (pluginId == null) {
           throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "No plug-in ID defined."));
       }
       if (pathInBundle == null) {
           throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "No path in plug-in defined."));
       }
       if (target == null) {
           throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "No target is defined."));
       }
       // Get Bundle.
       Bundle bundle = Platform.getBundle(pluginId);
       if (bundle == null) {
           throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Can't find plug-in with ID \"" + pluginId + "\"."));
       }
       // Search entries.
       Enumeration<?> entries = bundle.findEntries(pathInBundle, "*", true);
       if (entries != null) {
           // Make sure that target exists
           target.mkdirs();
           // Extract entries
           while (entries.hasMoreElements()) {
               Object entry = entries.nextElement();
               if (entry instanceof URL) {
                   URL url = (URL) entry;
                   String urlPath = url.getPath();
                   int pathInBundleIndex = urlPath.indexOf(pathInBundle);
                   String pathInTarget = urlPath.substring(pathInBundleIndex + pathInBundle.length());
                   InputStream in = null;
                   try {
                       FileOutputStream out = null;
                       try {
                           // Check if it is a file or folder by the content size.
                           URLConnection connection = url.openConnection();
                           if (connection.getContentLength() > 0) {
                               in = connection.getInputStream();
                               File file = new File(target, pathInTarget);
                               out = new FileOutputStream(file);
                               int read;
                               byte[] buffer = new byte[1024 * 10];
                               while ((read = in.read(buffer)) >= 0) {
                                   out.write(buffer, 0, read);
                               }
                           }
                           else {
                               // Handle URL as folder (Happens in product execution)
                               File folder = new File(target, pathInTarget);
                               if (!folder.exists()) {
                                   folder.mkdirs();
                               }
                           }
                       }
                       finally {
                           if (out != null) {
                               out.close();
                           }
                       }
                   }
                   catch (IOException e) {
                       // Handle URL as folder (This happens in IDE execution)
                       File folder = new File(target, pathInTarget);
                       if (!folder.exists()) {
                           folder.mkdirs();
                       }
                   }
                   finally {
                       try {
                           if (in != null) {
                               in.close();
                           }
                       }
                       catch (IOException e) {
                           // Nothing to do.
                       }
                   }
               }
               else {
                   throw new IllegalArgumentException("Unsupported bundle entry \"" + entry + "\".");
               }
           }
       }
   }
   
   /**
    * Extracts or files and folders form the bundle into the workspace target.
    * @param bundleId The ID of the bundle to extract from.
    * @param pathInBundle The path in the bundle.
    * @param target The target in the workspace.
    * @throws CoreException Occurred Exception.
    */
   public static void extractFromBundleToWorkspace(String bundleId,
                                                   String pathInBundle,
                                                   IContainer target) throws CoreException {
       // Make sure that all parameters are defined.
       if (bundleId == null) {
           throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "No plug-in ID defined."));
       }
       if (pathInBundle == null) {
           throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "No path in plug-in defined."));
       }
       if (target == null) {
           throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "No target is defined."));
       }
       // Get Bundle.
       Bundle bundle = Platform.getBundle(bundleId);
       if (bundle == null) {
           throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Can't find plug-in with ID \"" + bundleId + "\"."));
       }
       // Search entries.
       Enumeration<?> entries = bundle.findEntries(pathInBundle, "*", true);
       if (entries != null) {
           // Make sure that target exists
           if (!target.exists()) {
               if (target instanceof IFolder) {
                   ((IFolder)target).create(true, true, null);
               }
               else if (target instanceof IProject) {
                   IProject project = (IProject)target;
                   project.create(null);
                   if (!project.isOpen()) {
                       project.open(null);
                   }
               }
           }
           // Extract entries
           while (entries.hasMoreElements()) {
              Object entry = entries.nextElement();
              if (entry instanceof URL) {
                 URL url = (URL)entry;
                 String urlPath = url.getPath();
                 int pathInBundleIndex = urlPath.indexOf(pathInBundle);
                 String pathInTarget = urlPath.substring(pathInBundleIndex + pathInBundle.length());
                 try {
                    // Check if it is a file or folder by the content size.
                    URLConnection connection = url.openConnection();
                    if (connection.getContentLength() > 0) {
                       InputStream in = connection.getInputStream();
                       IFile file = target.getFile(new Path(pathInTarget));
                       if (file.exists()) {
                          file.setContents(in, true, true, null);
                       }
                       else {
                          file.create(in, true, null);
                       }
                    }
                    else {
                       // Handle URL as folder (Happens in product execution)
                       IFolder folder = target.getFolder(new Path(pathInTarget));
                       if (!folder.exists()) {
                          folder.create(true, true, null);
                       }
                    }
                 }
                 catch (IOException e) {
                     // Handle URL as folder (This happens in IDE execution)
                     IFolder folder = target.getFolder(new Path(pathInTarget));
                     if (!folder.exists()) {
                        folder.create(true, true, null);
                     }
                 }
              }
              else {
                 throw new IllegalArgumentException("Unsupported bundle entry \"" + entry + "\".");
              }
           }
       }
   }

   /**
    * Opens an {@link InputStream} to the resource in the plug-in with the given ID.
    * The caller of this method is responsible to close it.
    * @param bundleId The ID of the plug-in that contains the resource.
    * @param pathInBundle The path to the resource.
    * @return The opened {@link InputStream}.
    * @throws IOException Occurred Exception.
    */
   public static InputStream openInputStream(String bundleId, String pathInBundle) throws IOException {
       if (bundleId != null) {
           if (pathInBundle != null) {
               Bundle bundle = Platform.getBundle(bundleId);
               if (bundle != null) {
                   URL url = bundle.getEntry(pathInBundle);
                   if (url != null) {
                       return url.openStream();
                   }
                   else {
                       throw new IOException("Can't find resource \"" + pathInBundle + "\" in plug-in \"" + bundleId + "\".");
                   }
               }
               else {
                   throw new IOException("Can't find plug-in \"" + bundleId + "\".");
               }
           }
           else {
               throw new IOException("No path in plug-in \"" + bundleId + "\" defined.");
           }
       }
       else {
           throw new IOException("No plug-in defined.");
       }
   }
}