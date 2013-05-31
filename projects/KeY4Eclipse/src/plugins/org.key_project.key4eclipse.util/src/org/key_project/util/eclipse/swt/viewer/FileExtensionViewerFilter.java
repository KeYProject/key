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

package org.key_project.util.eclipse.swt.viewer;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.key_project.util.Activator;
import org.key_project.util.eclipse.Logger;
import org.key_project.util.java.StringUtil;

/**
 * This {@link ViewerFilter} can be used to filter {@link IFile}s by 
 * their file extensions ({@link IFile#getFileExtension()}).
 * @author Martin Hentschel
 */
public class FileExtensionViewerFilter extends ViewerFilter {
    /**
     * The accepted file extensions in lower case.
     */
    private Set<String> acceptedExtensions = new HashSet<String>();
    
    /**
     * Case sensitive file extension matching?
     */
    private boolean caseSensitive;
    
    /**
     * Constructor.
     * @param caseSensitive Case sensitive file extension matching?
     * @param acceptedExtensions The allowed file extensions.
     */
    public FileExtensionViewerFilter(boolean caseSensitive, String[] acceptedExtensions) {
        this.caseSensitive = caseSensitive;
        // Convert all file extension into lower case.
        if (acceptedExtensions != null) {
            for (String extension : acceptedExtensions) {
                if (extension != null) {
                    this.acceptedExtensions.add(caseSensitive ? extension : extension.toLowerCase());
                }
                else {
                    this.acceptedExtensions.add(StringUtil.EMPTY_STRING);
                }
            }
        }
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean select(Viewer viewer, Object parentElement, Object element) {
        try {
            if (element instanceof IFile) {
                // Check file extension.
                IFile file = (IFile)element;
                String extension = file.getFileExtension();
                if (extension == null) {
                    extension = StringUtil.EMPTY_STRING;
                }
                else if (!caseSensitive) {
                    extension = extension.toLowerCase();
                }
                return acceptedExtensions.contains(extension);
            }
            else if (element instanceof IContainer) {
                // Make sure that an IProject is open.
                if (element instanceof IProject && !((IProject)element).isOpen()) {
                   return false;
                }
                else {
                   // Make sure that it contains an accepted file.
                   IResource[] children = ((IContainer)element).members();
                   boolean childAccepted = false;
                   int i = 0;
                   while (!childAccepted && i < children.length) {
                       childAccepted = select(viewer, element, children[i]);
                       i++;
                   }
                   return childAccepted;
                }
            }
            else {
                return false; // Unknown elements.
            }
        }
        catch (CoreException e) {
            new Logger(Activator.getDefault(), Activator.PLUGIN_ID).logError(e);
            return false;
        }
    }
}