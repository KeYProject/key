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

package org.key_project.util.eclipse.swt.dialog;

import org.eclipse.jface.viewers.IBaseLabelProvider;
import org.eclipse.jface.viewers.IContentProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.dialogs.ElementTreeSelectionDialog;

/**
 * <p>
 * A dialog to select elements in a list structure which is shown
 * via a {@link TableViewer}.
 * </p>
 * <p>
 * The usage and the implementation is oriented on {@link ElementTreeSelectionDialog}.
 * </p>
 * @author Martin Hentschel
 */
public class ElementTableSelectionDialog extends AbstractElementSelectionDialog<TableViewer> {
   /**
    * Constructor.
    * @param parent The parent {@link Shell}.
    * @param contentProvider The content provider to use.
    * @param labelProvider The label provider to use.
    */
   public ElementTableSelectionDialog(Shell parent, 
                                      IContentProvider contentProvider, 
                                      IBaseLabelProvider labelProvider) {
      super(parent, contentProvider, labelProvider);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected TableViewer createViewerInstance(Composite parent) {
      return new TableViewer(parent, SWT.BORDER | (isAllowMultiple() ? SWT.MULTI : SWT.SINGLE));
   }
}