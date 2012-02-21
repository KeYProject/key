package org.key_project.automaticverifier.product.ui.provider;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.automaticverifier.product.ui.model.AutomaticProof;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.Proof;

/**
 * An {@link ITableLabelProvider} implementation for {@link AutomaticProof} instances.
 * @author Martin Hentschel
 */
public class AutomaticProofLabelProvider extends LabelProvider implements ITableLabelProvider {
    /**
     * Listens for changes on observed {@link AutomaticProof} instances.
     */
    private PropertyChangeListener listener = new PropertyChangeListener() {
        @Override
        public void propertyChange(PropertyChangeEvent evt) {
            handlePropertyChange(evt);
        }
    };
    
    /**
     * Contains all observed {@link AutomaticProof} instances.
     */
    private Set<AutomaticProof> observedProofs = new HashSet<AutomaticProof>();
    
    /**
     * {@inheritDoc}
     */
    @Override
    public Image getColumnImage(Object element, int columnIndex) {
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getColumnText(Object element, int columnIndex) {
        if (element instanceof AutomaticProof) {
            AutomaticProof proof = (AutomaticProof)element;
            addListenerTo(proof);
            switch (columnIndex) {
                case 0 : return proof.getTypeName();
                case 1 : return proof.getOperationName();
                case 2 : return proof.getContractName();
                case 3 : return proof.getResult() != null ? proof.getResult().getDisplayText() : StringUtil.EMPTY_STRING;
                default : return getText(element);
            }
        }
        else {
            return getText(element);
        }
    }

    /**
     * Adds the listener to the given {@link Proof} if required.
     * @param proof The {@link Proof} to observe.
     */
    protected void addListenerTo(AutomaticProof proof) {
        if (proof != null && !proof.hasListener(AutomaticProof.PROP_RESULT, listener)) {
            proof.addPropertyChangeListener(AutomaticProof.PROP_RESULT, listener);
        }
    }

    /**
     * When something has changed on an observed {@link AutomaticProof}.
     * @param evt The event.
     */
    protected void handlePropertyChange(final PropertyChangeEvent evt) {
        if (Display.getDefault() != null && !Display.getDefault().isDisposed()) {
            Display.getDefault().syncExec(new Runnable() {
                @Override
                public void run() {
                    fireLabelProviderChanged(new LabelProviderChangedEvent(AutomaticProofLabelProvider.this, evt.getSource()));
                }
            });
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void dispose() {
        for (AutomaticProof proof : observedProofs) {
            removeListenerFrom(proof);
        }
        observedProofs.clear();
        super.dispose();
    }

    /**
     * Removes the listener from the given {@link Proof}.
     * @param proof The {@link Proof} to no longer observe.
     */
    protected void removeListenerFrom(AutomaticProof proof) {
        if (proof != null) {
            proof.removePropertyChangeListener(AutomaticProof.PROP_RESULT, listener);
        }
    }
}
