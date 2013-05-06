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

package org.key_project.sed.ui.menu.contribution;

import org.eclipse.jface.action.ContributionItem;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MenuEvent;
import org.eclipse.swt.events.MenuListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.MenuItem;
import org.key_project.sed.core.util.SEDPreferenceUtil;

/**
 * Adds the menu item "Show &compact symbolic execution tree" to the parent
 * menu. A {@link MenuListener} makes sure that the checked state of the
 * menu item is always equal to {@link SEDPreferenceUtil#isShowCompactExecutionTree()}
 * when it is visible. When the user clicks on the menu item the value
 * of {@link SEDPreferenceUtil#isShowCompactExecutionTree()} is toggled
 * via {@link SEDPreferenceUtil#toggleShowCompactExecutionTreePreference()}.
 * @author Martin Hentschel
 */
public class ToggleShowCompactSymbolicExecutionTreeContributionItem extends ContributionItem {
   /**
    * Constructor.
    */
   public ToggleShowCompactSymbolicExecutionTreeContributionItem() {
   }

   /**
    * Constructor.
    * @param id The ID of this item.
    */
   public ToggleShowCompactSymbolicExecutionTreeContributionItem(String id) {
      super(id);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void fill(Menu menu, int index) {
      super.fill(menu, index);
      final MenuItem item = new MenuItem(menu, SWT.CHECK);
      item.setText("Show &compact symbolic execution tree");
      item.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            SEDPreferenceUtil.toggleShowCompactExecutionTreePreference();
         }
      });
      menu.addMenuListener(new MenuListener() {
         @Override
         public void menuShown(MenuEvent e) {
            item.setSelection(SEDPreferenceUtil.isShowCompactExecutionTree());
         }
         
         @Override
         public void menuHidden(MenuEvent e) {
         }
      });
   }
}