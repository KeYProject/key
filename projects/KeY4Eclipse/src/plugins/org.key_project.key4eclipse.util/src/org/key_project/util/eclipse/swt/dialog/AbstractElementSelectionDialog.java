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

import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.viewers.IBaseLabelProvider;
import org.eclipse.jface.viewers.IContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredViewer;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.dialogs.ElementTreeSelectionDialog;
import org.eclipse.ui.dialogs.SelectionStatusDialog;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * <p>
 * A basic implementation of a dialog to select elements in a list structure which is shown
 * via a {@link StructuredViewer}.
 * </p>
 * <p>
 * The usage and the implementation is oriented on {@link ElementTreeSelectionDialog}.
 * </p>
 * @author Martin Hentschel
 */
public abstract class AbstractElementSelectionDialog<V extends StructuredViewer> extends SelectionStatusDialog {
    /**
     * The content provider of {@link #viewer}.
     */
    private IContentProvider contentProvider;
    
    /**
     * The label provider of {@link #viewer}.
     */
    private IBaseLabelProvider labelProvider;

    /**
     * The input in {@link #viewer}.
     */
    private Object input;
    
    /**
     * The viewer.
     */
    private V viewer;
    
    /**
     * Allow multiple selections?
     */
    private boolean allowMultiple;

    /**
     * Constructor.
     * @param parent The parent {@link Shell}.
     * @param contentProvider The content provider to use.
     * @param labelProvider The label provider to use.
     */
    public AbstractElementSelectionDialog(Shell parent, 
                                       IContentProvider contentProvider,
                                       IBaseLabelProvider labelProvider) {
        super(parent);
        this.contentProvider = contentProvider;
        this.labelProvider = labelProvider;
        setResult(new LinkedList<Object>());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Control createDialogArea(Composite parent) {
        Composite contents = (Composite) super.createDialogArea(parent);

        createMessageArea(contents);
        viewer = createViewer(contents);

        setViewerContent(contentProvider, labelProvider, input);

        List<?> iniitalSelection = getInitialElementSelections();
        setSelection(SWTUtil.createSelection(iniitalSelection));

        return contents;
    }

    /**
     * Creates the viewer.
     * @param parent The parent {@link Composite}.
     * @return The created viewer.
     */
    protected V createViewer(Composite parent) {
        // Create viewer layout
        int fWidth = 60;
        int fHeight = 18;    
        GridData data = new GridData();
        data.widthHint = convertWidthInCharsToPixels(fWidth);
        data.heightHint = convertHeightInCharsToPixels(fHeight);
        data.grabExcessVerticalSpace = true;
        data.grabExcessHorizontalSpace = true;
        data.horizontalAlignment = GridData.FILL;
        data.verticalAlignment = GridData.FILL;
        // Create viewer
        V createdViewer = createViewerInstance(parent);
        createdViewer.getControl().setLayoutData(data);
        return createdViewer;
    }
    
    /**
     * Creates the {@link StructuredViewer} instance.
     * @param parent The parent {@link Composite}.
     * @return The created {@link StructuredViewer}.
     */
    protected abstract V createViewerInstance(Composite parent);
    
    /**
     * Sets the content in the viewer.
     * @param contentProvider The content provider to use.
     * @param labelProvider The label provider to use.
     * @param input The input to use.
     */
    protected void setViewerContent(IContentProvider contentProvider,
                                    IBaseLabelProvider labelProvider,
                                    Object input) {
        viewer.setContentProvider(contentProvider);
        viewer.setLabelProvider(labelProvider);
        viewer.setInput(input);
    }

    /**
     * Sets the selection.
     * @param selection The selection to set.
     */
    protected void setSelection(ISelection selection) {
        viewer.setSelection(selection);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void computeResult() {
        if (viewer.getSelection() instanceof IStructuredSelection) {
            setResult(((IStructuredSelection)viewer.getSelection()).toList());
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void cancelPressed() {
        setResult(new LinkedList<Object>());
        super.cancelPressed();
    }
    
    /**
     * Returns the input.
     * @return The input.
     */
    public Object getInput() {
        return input;
    }

    /**
     * Sets the input.
     * @param input The input to set.
     */
    public void setInput(Object input) {
        this.input = input;
    }
    
    /**
     * Checks if multiple selections are allowed.
     * @return {@code true} multiple selections are allowed, {@code false} only single selection is allowed.
     */
    public boolean isAllowMultiple() {
        return allowMultiple;
    }

    /**
     * Defines if multiple selections are allowed.
     * @param allowMultiple {@code true} multiple selections are allowed, {@code false} only single selection is allowed.
     */
    public void setAllowMultiple(boolean allowMultiple) {
        this.allowMultiple = allowMultiple;
    }
    
    /**
     * Returns the defined {@link IContentProvider}.
     * @return The defined {@link IContentProvider}.
     */
    protected IContentProvider getContentProvider() {
        return contentProvider;
    }

    /**
     * Returns the defined {@link IBaseLabelProvider}.
     * @return The defined {@link IBaseLabelProvider}.
     */
    protected IBaseLabelProvider getLabelProvider() {
        return labelProvider;
    }
}