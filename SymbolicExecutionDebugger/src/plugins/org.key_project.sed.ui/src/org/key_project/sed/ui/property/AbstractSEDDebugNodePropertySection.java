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

package org.key_project.sed.ui.property;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * Provides the basic implementation of {@link AbstractPropertySection}s
 * which shows content of an {@link ISEDDebugNode}.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDDebugNodePropertySection extends AbstractPropertySection {
   /**
    * The shown content.
    */
   private ISEDDebugNodeTabContent content;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      content = createContent();
      content.createComposite(parent, getWidgetFactory());
   }

   /**
    * Creates the {@link ISEDDebugNodeTabContent} which shows the content.
    * @return The created {@link ISEDDebugNodeTabContent}.
    */
   protected abstract ISEDDebugNodeTabContent createContent();

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      content.updateContent(getDebugNode());
   }
   
   /**
    * Returns the {@link ISEDDebugNode} to show.
    * @return The {@link ISEDDebugNode} to show or {@code null} if no one should be shown.
    */
   protected ISEDDebugNode getDebugNode() {
      Object object = SWTUtil.getFirstElement(getSelection());
      return getDebugNode(object);
   }
   
   /**
    * Converts the given {@link Object} into an {@link ISEDDebugNode} if possible.
    * @param object The given {@link Object}.
    * @return The {@link ISEDDebugNode} or {@code null} if conversion is not possible.
    */
   public static ISEDDebugNode getDebugNode(Object object) {
      return object instanceof ISEDDebugNode ? (ISEDDebugNode)object : null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (content != null) {
         content.dispose();
      }
      super.dispose();
   }
}