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

package org.key_project.sed.key.ui.property;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * {@link ISection} implementation to show the properties of {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 */
public class KeYDebugNodePropertySection extends AbstractPropertySection {
   /**
    * The shown content.
    */
   private KeYTabComposite contentComposite;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      contentComposite = new KeYTabComposite(parent, SWT.NONE, getWidgetFactory());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      contentComposite.updateContent(getDebugNode());
   }
   
   /**
    * Returns the {@link ISEDDebugNode} to show.
    * @return The {@link ISEDDebugNode} to show or {@code null} if no one should be shown.
    */
   protected IKeYSEDDebugNode<?> getDebugNode() {
      Object object = SWTUtil.getFirstElement(getSelection());
      return getDebugNode(object);
   }
   
   /**
    * Converts the given {@link Object} into an {@link IKeYSEDDebugNode} if possible.
    * @param object The given {@link Object}.
    * @return The {@link IKeYSEDDebugNode} or {@code null} if conversion is not possible.
    */
   public static IKeYSEDDebugNode<?> getDebugNode(Object object) {
      return object instanceof IKeYSEDDebugNode<?> ? (IKeYSEDDebugNode<?>)object : null;
   }
}