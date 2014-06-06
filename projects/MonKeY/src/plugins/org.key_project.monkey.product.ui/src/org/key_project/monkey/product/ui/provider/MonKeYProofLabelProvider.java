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

package org.key_project.monkey.product.ui.provider;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.monkey.product.ui.model.MonKeYProof;
import org.key_project.monkey.product.ui.model.MonKeYProofResult;
import org.key_project.monkey.product.ui.util.MonKeYUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.Proof;

/**
 * An {@link ITableLabelProvider} implementation for {@link MonKeYProof} instances.
 * @author Martin Hentschel
 */
public class MonKeYProofLabelProvider extends LabelProvider implements ITableLabelProvider {
    /**
     * Listens for changes on observed {@link MonKeYProof} instances.
     */
    private PropertyChangeListener listener = new PropertyChangeListener() {
        @Override
        public void propertyChange(PropertyChangeEvent evt) {
            handlePropertyChange(evt);
        }
    };
    
    /**
     * Contains all observed {@link MonKeYProof} instances.
     */
    private Set<MonKeYProof> observedProofs = new HashSet<MonKeYProof>();
    
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
        if (element instanceof MonKeYProof) {
            MonKeYProof proof = (MonKeYProof)element;
            addListenerTo(proof);
            switch (columnIndex) {
                case 0 : return proof.getTypeName();
                case 1 : return proof.getTargetName();
                case 2 : return proof.getContractName();
                case 3 : return proof.getReuseStatus();
                case 4 : return proof.getResult() != null ? proof.getResult().getDisplayText() : StringUtil.EMPTY_STRING;
                case 5 : return proof.hasResult() ? proof.getNodes() + StringUtil.EMPTY_STRING : StringUtil.EMPTY_STRING;
                case 6 : return proof.hasResult() ? proof.getBranches() + StringUtil.EMPTY_STRING : StringUtil.EMPTY_STRING;
                case 7 : return proof.hasResult() ? proof.getTime() + StringUtil.EMPTY_STRING : StringUtil.EMPTY_STRING;
                case 8 : return proof.hasResult() & !MonKeYProofResult.CLOSED.equals(proof.getResult()) ? MonKeYUtil.toString(proof.isHasGoalWithApplicableRules()) : StringUtil.EMPTY_STRING;
                case 9 : return proof.hasResult() & !MonKeYProofResult.CLOSED.equals(proof.getResult()) ? MonKeYUtil.toString(proof.isHasGoalWithoutApplicableRules()) : StringUtil.EMPTY_STRING;
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
    protected void addListenerTo(MonKeYProof proof) {
        if (proof != null && !proof.hasListener(listener)) {
            proof.addPropertyChangeListener(listener);
        }
    }

    /**
     * When something has changed on an observed {@link MonKeYProof}.
     * @param evt The event.
     */
    protected void handlePropertyChange(final PropertyChangeEvent evt) {
        if (Display.getDefault() != null && !Display.getDefault().isDisposed()) {
            Display.getDefault().syncExec(new Runnable() {
                @Override
                public void run() {
                    fireLabelProviderChanged(new LabelProviderChangedEvent(MonKeYProofLabelProvider.this, evt.getSource()));
                }
            });
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void dispose() {
        for (MonKeYProof proof : observedProofs) {
            removeListenerFrom(proof);
        }
        observedProofs.clear();
        super.dispose();
    }

    /**
     * Removes the listener from the given {@link Proof}.
     * @param proof The {@link Proof} to no longer observe.
     */
    protected void removeListenerFrom(MonKeYProof proof) {
        if (proof != null) {
            proof.removePropertyChangeListener(listener);
        }
    }
}