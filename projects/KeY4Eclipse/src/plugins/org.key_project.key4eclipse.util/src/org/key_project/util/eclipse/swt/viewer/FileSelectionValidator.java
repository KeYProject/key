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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.dialogs.ISelectionStatusValidator;
import org.key_project.util.Activator;
import org.key_project.util.eclipse.Logger;

/**
 * An {@link ISelectionStatusValidator} that can be used to verify
 * that {@link IFile}s are selected.
 * @author Martin Hentschel
 */
public class FileSelectionValidator implements ISelectionStatusValidator {
    /**
     * Accept empty selections?
     */
    private boolean acceptEmptySelection;
    
    /**
     * Allow multiple selections?
     */
    private boolean allowMultiSelection;
    
    /**
     * Constructor.
     * @param acceptEmptySelection Accept empty selections?
     * @param allowMultiSelection Allow multiple selections?
     */
    public FileSelectionValidator(boolean acceptEmptySelection, 
                                  boolean allowMultiSelection) {
        super();
        this.acceptEmptySelection = acceptEmptySelection;
        this.allowMultiSelection = allowMultiSelection;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IStatus validate(Object[] selection) {
        if (selection != null && selection.length >= 1) {
            // Not empty selection, validate each entry
            for (Object obj : selection) {
                if (!(obj instanceof IFile)) {
                    return new Logger(Activator.getDefault(), Activator.PLUGIN_ID).createErrorStatus("The resource \"" + obj + "\" is no file.");
                }
            }
            // Validate maximal selection
            if (allowMultiSelection || selection.length == 1) {
                return Status.OK_STATUS;
            }
            else {
                return new Logger(Activator.getDefault(), Activator.PLUGIN_ID).createErrorStatus("Multiple files are selected.");
            }
        }
        else {
            // Empty selection
            if (acceptEmptySelection) {
                return Status.OK_STATUS;
            }
            else {
                return new Logger(Activator.getDefault(), Activator.PLUGIN_ID).createErrorStatus("No file selected.");
            }
        }
    }
}