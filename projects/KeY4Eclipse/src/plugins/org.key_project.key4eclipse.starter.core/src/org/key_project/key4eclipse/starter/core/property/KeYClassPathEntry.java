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

package org.key_project.key4eclipse.starter.core.property;

import java.io.File;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

/**
 * Represents a class path entry for KeY.
 * @author Martin Hentschel
 */
public class KeYClassPathEntry {
    /**
     * The possible kinds.
     * @author Martin Hentschel
     */
    public static enum KeYClassPathEntryKind {
        /**
         * Entry in workspace.
         */
        WORKSPACE,
        
        /**
         * Entry in file system.
         */
        EXTERNAL_IN_FILE_SYSTEM
    }

    /**
     * The kind.
     */
    private KeYClassPathEntryKind kind;
    
    /**
     * The path.
     */
    private String path;

    /**
     * Constructor.
     * @param kind The kind.
     * @param path The path.
     */
    public KeYClassPathEntry(KeYClassPathEntryKind kind, String path) {
        this.kind = kind;
        this.path = path;
    }

    /**
     * Returns the kind.
     * @return The kind.
     */
    public KeYClassPathEntryKind getKind() {
        return kind;
    }

    /**
     * Returns the path.
     * @return The path.
     */
    public String getPath() {
        return path;
    }
    
    /**
     * Returns the {@link IResource} represented by this {@link KeYClassPathEntry}.
     * @return The {@link IResource} or {@code null} if no {@link IResource} is represented.
     */
    public IResource getResource() {
        if (KeYClassPathEntryKind.WORKSPACE.equals(getKind())) {
            return ResourcesPlugin.getWorkspace().getRoot().findMember(new Path(path));
        }
        else {
            return null;
        }
    }
    
    /**
     * Returns the local {@link File} reference.
     * @return The local {@link File} reference.
     */
    public File getLocation() {
        IResource resource = getResource();
        if (resource != null) {
            return ResourceUtil.getLocation(resource);
        }
        else {
            return new File(getPath());
        }
    }
    
    /**
     * Checks if this entry is valid.
     * @return {@code true} valid, {@code false} invalid.
     */
    public boolean isValid() {
        if (!StringUtil.isTrimmedEmpty(getPath())) {
            if (KeYClassPathEntryKind.WORKSPACE.equals(getKind())) {
                IResource resource = getResource();
                return resource != null && resource.exists();
            }
            else if (KeYClassPathEntryKind.EXTERNAL_IN_FILE_SYSTEM.equals(getKind())) {
                File file = getLocation();
                return file.exists();
            }
            else {
                return false;
            }
        }
        else {
            return false;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(Object obj) {
        if (obj instanceof KeYClassPathEntry) {
            KeYClassPathEntry other = (KeYClassPathEntry)obj;
            return ObjectUtil.equals(getKind(), other.getKind()) &&
                   ObjectUtil.equals(getPath(), other.getPath());
        }
        else {
            return false;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return ObjectUtil.hashCode(getKind()) +
               ObjectUtil.hashCode(getPath());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return getPath() + " [" + getKind() + "]";
    }
}