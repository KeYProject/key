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

package org.key_project.key4eclipse.common.ui.property;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.dialogs.PropertyPage;
import org.key_project.key4eclipse.common.ui.composite.ManageKeYClassPathComposite;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry.KeYPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;

/**
 * Provides the {@link PropertyPage} that is used to configure KeY specific
 * settings of an {@link IProject}.
 * @author Martin Hentschel
 */
public class KeYIncludesPropertyPage extends AbstractProjectPropertyPage {
   private ManageKeYClassPathComposite includesComposite;

   /**
     * {@inheritDoc}
     */
    @Override
    protected Control createContents(Composite parent) {
       initializeDialogUnits(parent);
       // Includes composite
       includesComposite = new ManageKeYClassPathComposite(parent, SWT.NONE, "Includes", false, false, "key");
       includesComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
       includesComposite.addPropertyChangeListener(ManageKeYClassPathComposite.PROP_CLASS_PATH_ENTRIES, new PropertyChangeListener() {
          @Override
          public void propertyChange(PropertyChangeEvent evt) {
             updateValidState();
          }
       });
       // Initialize UI controls
       try {
           IProject project = getProject();
           if (project != null) {
               includesComposite.setClassPathEntries(KeYResourceProperties.getIncludeEntries(project));
               includesComposite.setEnabled(true);
           }
           else {
              includesComposite.setEnabled(false);
           }
       }
       catch (CoreException e) {
           LogUtil.getLogger().logError(e);
           includesComposite.setEnabled(false);
       }
       finally {
           updateValidState();
       }
       return includesComposite;
    }

    /**
     * Updates the valid state.
     */
    protected void updateValidState() {
        boolean valid = true;
        // Validate class paths
        List<KeYPathEntry> classPathEntries = includesComposite.getClassPathEntries();
        if (valid && classPathEntries != null) {
            Iterator<KeYPathEntry> iter = classPathEntries.iterator();
            while (valid && iter.hasNext()) {
                KeYPathEntry next = iter.next();
                if (!next.isValid()) {
                    valid = false;
                    setErrorMessage("The include entry \"" + next.getPath() + "\" refers to a not existing " + (KeYPathEntryKind.WORKSPACE.equals(next.getKind()) ? "workspace resource" : "external resource") + ".");
                }
            }
        }
        // Update valid state
        setValid(valid);
        if (valid) {
            setErrorMessage(null);
        }
    }

   /**
     * {@inheritDoc}
     */
    @Override
    public boolean performOk() {
        try {
            IProject project = getProject();
            KeYResourceProperties.setIncludeEntries(project, includesComposite.getClassPathEntries());
            return super.performOk();
        }
        catch (CoreException e) {
            LogUtil.getLogger().logError(e);
            LogUtil.getLogger().openErrorDialog(getShell(), e);
            return false;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void performDefaults() {
       includesComposite.setClassPathEntries(new LinkedList<KeYPathEntry>());
       super.performDefaults();
    }
}