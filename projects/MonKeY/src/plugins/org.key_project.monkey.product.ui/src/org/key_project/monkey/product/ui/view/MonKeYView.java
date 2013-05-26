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

package org.key_project.monkey.product.ui.view;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.monkey.product.ui.composite.MonKeYComposite;

/**
 * Implementation of the view "MonKeY".
 * @author Martin Hentschel
 */
public class MonKeYView extends ViewPart {
    /**
     * The ID of this view.
     */
    public static final String ID = "org.key_project.monkey.product.ui.view.MonKeYView";

    /**
     * The shown {@link MonKeYComposite}.
     */
    private MonKeYComposite composite;
    
    /**
     * The {@link IMemento} to load the last state from.
     */
    private IMemento mementoToLoadFrom;
    
    /**
     * {@inheritDoc}
     */
    @Override
    public void createPartControl(Composite parent) {
        composite = new MonKeYComposite(parent, SWT.NONE);
        if (mementoToLoadFrom != null) {
            composite.loadState(mementoToLoadFrom);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void setFocus() {
        if (composite != null && !composite.isDisposed()) {
            composite.setFocus();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void init(IViewSite site, IMemento memento) throws PartInitException {
        super.init(site, memento);
        this.mementoToLoadFrom = memento;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void saveState(IMemento memento) {
        composite.saveState(memento);
        super.saveState(memento);
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
        if (IProofProvider.class.equals(adapter)) {
            return composite;
        }
        else {
            return super.getAdapter(adapter);
        }
    }
}