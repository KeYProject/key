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

import org.eclipse.core.resources.IResource;

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
}
