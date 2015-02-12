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

import org.eclipse.debug.core.model.IVariable;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * Provides the basic implementation of {@link AbstractPropertySection}s
 * which shows content of an {@link IVariable}.
 * @author Martin Hentschel
 */
public abstract class AbstractVariablePropertySection extends AbstractPropertySection {
   /**
    * The shown content.
    */
   private IVariableTabContent content;
   
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
    * Creates the {@link IVariableTabContent} which shows the content.
    * @return The created {@link IVariableTabContent}.
    */
   protected abstract IVariableTabContent createContent();

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      content.updateContent(getVariable());
   }
   
   /**
    * Returns the {@link IVariable} to show.
    * @return The {@link IVariable} to show or {@code null} if no one should be shown.
    */
   protected IVariable getVariable() {
      Object object = SWTUtil.getFirstElement(getSelection());
      return getVariable(object);
   }
   
   /**
    * Converts the given {@link Object} into an {@link IVariable} if possible.
    * @param object The given {@link Object}.
    * @return The {@link IVariable} or {@code null} if conversion is not possible.
    */
   public static IVariable getVariable(Object object) {
      return object instanceof IVariable ? (IVariable)object : null;
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