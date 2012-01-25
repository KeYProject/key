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

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Enumeration;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
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
    * Extracts or files and folders form the bundle into the workspace target.
    * @param bundleId The ID of the bundle to extract from.
    * @param pathInBundle The path in the bundle.
    * @param target The target in the workspace.
    * @throws CoreException Occurred Exception.
    */
   public static void extractFromBundleToWorkspace(String bundleId,
                                                   String pathInBundle,
                                                   IContainer target) throws CoreException {
      Bundle bundle = Platform.getBundle(bundleId);
      Assert.isNotNull(bundle);
      Enumeration<?> entries = bundle.findEntries(pathInBundle, "*", true);
      while (entries.hasMoreElements()) {
         Object entry = entries.nextElement();
         if (entry instanceof URL) {
            URL url = (URL)entry;
            String urlPath = url.getPath();
            int pathInBundleIndex = urlPath.indexOf(pathInBundle);
            String pathInTarget = urlPath.substring(pathInBundleIndex + pathInBundle.length());
            try {
               // Check if it is a file by opening an input stream
               InputStream in = url.openStream();
               IFile file = target.getFile(new Path(pathInTarget));
               if (file.exists()) {
                  file.setContents(in, true, true, null);
               }
               else {
                  file.create(in, true, null);
               }
            }
            catch (IOException e) {
               // Handle URL as folder
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
