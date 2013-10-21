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

package org.key_project.key4eclipse.common.ui.dialog;

import org.eclipse.jface.viewers.IContentProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.key_project.key4eclipse.common.ui.provider.ContractLabelProvider;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.dialog.ElementTableSelectionDialog;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;

/**
 * A special {@link ElementTableSelectionDialog} that is used
 * to select {@link Contract}s.
 * @author Martin Hentschel
 */
public class ContractSelectionDialog extends ElementTableSelectionDialog {
    /**
     * Constructor.
     * @param parent The parent {@link Shell}.
     * @param contentProvider The content provider to use.
     * @param services The {@link Services} to use.
     */
    public ContractSelectionDialog(Shell parent, IContentProvider contentProvider, Services services) {
        super(parent, contentProvider, new ContractLabelProvider(services));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected TableViewer createViewer(Composite parent) {
        TableViewer viewer = super.createViewer(parent);
        viewer.getTable().setLinesVisible(true);
        SWTUtil.makeTableShowingFullTableItemImages(viewer.getTable());
        return viewer;
    }
}