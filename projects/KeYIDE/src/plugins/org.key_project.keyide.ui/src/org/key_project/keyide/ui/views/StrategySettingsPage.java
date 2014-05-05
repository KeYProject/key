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

package org.key_project.keyide.ui.views;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.part.Page;
import org.key_project.key4eclipse.common.ui.composite.StrategySettingsComposite;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.keyide.ui.editor.KeYEditor;

import de.uka.ilkd.key.proof.Proof;

/**
 * The default {@link IStrategySettingsPage} returned by the {@link KeYEditor}
 * to show the strategy settings in a {@link StrategySettingsComposite}.
 * @author Martin Hentschel
 */
public class StrategySettingsPage extends Page implements IStrategySettingsPage {
   /**
    * The {@link IProofProvider} which provides the {@link Proof}s.
    */
   private IProofProvider proofProvider;
   
   /**
    * The {@link StrategySettingsComposite} which is used to edit the strategy settings.
    */
   private StrategySettingsComposite composite;

   /**
    * Constructor.
    * @param proofProvider The {@link IProofProvider} which provides the {@link Proof}s.
    */
   public StrategySettingsPage(IProofProvider proofProvider) {
      this.proofProvider = proofProvider;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      composite = new StrategySettingsComposite(parent, proofProvider);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Control getControl() {
      return composite;
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
   public void dispose() {
      if (composite != null) {
         composite.dispose();
      }
      super.dispose();
   }
}