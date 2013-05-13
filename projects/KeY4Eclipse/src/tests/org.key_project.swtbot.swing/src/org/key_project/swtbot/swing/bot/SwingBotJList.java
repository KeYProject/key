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

package org.key_project.swtbot.swing.bot;

import java.awt.Component;

import javax.swing.JList;
import javax.swing.ListModel;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotList;
import org.key_project.swtbot.swing.util.AbstractRunnableWithResult;
import org.key_project.swtbot.swing.util.IRunnableWithResult;
import org.key_project.swtbot.swing.util.SaveSwingUtil;

/**
 * <p>
 * This represents a {@link JList} {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link SWTBotList}.
 * </p>
 * @author Martin Hentschel
 */
public class SwingBotJList extends AbstractSwingBotComponent<JList> {
   /**
    * Constructs an instance of this object with the given {@link JList}.
    * @param component The given {@link JList}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */      
   public SwingBotJList(JList component) throws WidgetNotFoundException {
      super(component);
   }
   
   /**
    * Selects the index in the {@link JList}.
    * @param index The index to select.
    */
   public void select(final int index) {
      SaveSwingUtil.invokeAndWait(new Runnable() {
         @Override
         public void run() {
            component.setSelectedIndex(index);
         }
      });
   }

   /**
    * Returns the selected {@link Object}s.
    * @return The selected {@link Object}s.
    */   
   public Object[] getSelectedObjects() {
      IRunnableWithResult<Object[]> run = new AbstractRunnableWithResult<Object[]>() {
         @Override
         public void run() {
            Object[] result = component.getSelectedValues();
            if (result != null) {
               setResult(result);
            }
            else {
               setResult(new Object[0]);
            }
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      return run.getResult();
   }

   /**
    * Selects the object with the given text, if it was not found
    * all items are deselected.
    * @param itemText The text of the item to select.
    */
   public void selectByText(final String itemText) {
      SaveSwingUtil.invokeAndWait(new Runnable() {
         @Override
         public void run() {
            Object toSelect = null;
            ListModel model = component.getModel();
            int i = 0;
            while (toSelect == null && i < model.getSize()) {
               Object current = model.getElementAt(i);
               if (current != null && current.toString().equals(itemText)) {
                  toSelect = current;
               }
               i++;
            }
            if (toSelect != null) {
               component.setSelectedValue(toSelect, true);
            }
            else {
               component.setSelectedIndices(new int[0]);
            }
         }
      });
   }
}