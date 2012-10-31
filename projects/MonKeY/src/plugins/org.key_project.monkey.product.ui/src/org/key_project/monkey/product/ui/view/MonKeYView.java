package org.key_project.monkey.product.ui.view;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;
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
}
