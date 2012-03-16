package org.key_project.automaticverifier.product.ui.view;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;
import org.key_project.automaticverifier.product.ui.composite.AutomaticVerifierComposite;

/**
 * Implementation of the view "Automatic Verifier".
 * @author Martin Hentschel
 */
public class AutomaticVerifierView extends ViewPart {
    /**
     * The ID of this view.
     */
    public static final String ID = "org.key_project.automaticverifier.product.ui.view.AutomaticVerifierView";

    /**
     * The shown {@link AutomaticVerifierComposite}.
     */
    private AutomaticVerifierComposite composite;
    
    /**
     * The {@link IMemento} to load the last state from.
     */
    private IMemento mementoToLoadFrom;
    
    /**
     * {@inheritDoc}
     */
    @Override
    public void createPartControl(Composite parent) {
        composite = new AutomaticVerifierComposite(parent, SWT.NONE);
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
