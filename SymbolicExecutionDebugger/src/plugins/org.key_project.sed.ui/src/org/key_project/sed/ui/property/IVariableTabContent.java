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
import org.eclipse.ui.services.IDisposable;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;

/**
 * Defines the functionality required to show content in an {@link IVariable}.
 * @author Martin Hentschel
 */
public interface IVariableTabContent extends IDisposable {
   /**
    * Creates the UI controls shown to the user.
    * @param parent The parent {@link Composite}.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   public void createComposite(Composite parent, TabbedPropertySheetWidgetFactory factory);

   /**
    * Updates the shown content.
    * @param variable The {@link IVariable} which provides the new content.
    */
   public void updateContent(IVariable variable);
}