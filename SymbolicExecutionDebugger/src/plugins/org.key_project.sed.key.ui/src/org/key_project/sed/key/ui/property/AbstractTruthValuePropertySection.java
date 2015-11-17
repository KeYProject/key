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

package org.key_project.sed.key.ui.property;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.ui.property.AbstractTruthValueComposite.ILayoutListener;

/**
 * Basic {@link ISection} implementation to show the properties of {@link ISENode}s
 * within a {@link AbstractTruthValueComposite}.
 * @author Martin Hentschel
 */
public abstract class AbstractTruthValuePropertySection extends AbstractPropertySection implements ILayoutListener {
   /**
    * The shown content.
    */
   private AbstractTruthValueComposite contentComposite;
   
   /**
    * The {@link TabbedPropertySheetPage} this {@link AbstractPropertySection} is shown in.
    */
   private TabbedPropertySheetPage tabbedPropertySheetPage;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      this.tabbedPropertySheetPage = tabbedPropertySheetPage;
      super.createControls(parent, tabbedPropertySheetPage);
      contentComposite = createContentComposite(parent);
   }
   
   /**
    * Creates the {@link AbstractTruthValueComposite} to show.
    * @param parent The parent {@link Composite}.
    * @return The created {@link AbstractTruthValueComposite}.
    */
   protected abstract AbstractTruthValueComposite createContentComposite(Composite parent);

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (contentComposite != null) {
         contentComposite.dispose();
      }
      super.dispose();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      contentComposite.updateContent(getDebugNode());
   }
   
   /**
    * Returns the {@link IKeYSENode} to show.
    * @return The {@link IKeYSENode} to show or {@code null} if no one should be shown.
    */
   protected abstract IKeYSENode<?> getDebugNode();

   /**
    * {@inheritDoc}
    */
   @Override
   public void layoutUpdated() {
      if (tabbedPropertySheetPage != null) {
         tabbedPropertySheetPage.resizeScrolledComposite();
      }
   }
}