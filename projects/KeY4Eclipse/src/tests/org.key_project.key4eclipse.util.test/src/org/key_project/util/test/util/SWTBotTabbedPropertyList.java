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

package org.key_project.util.test.util;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory;
import org.eclipse.swtbot.swt.finder.results.BoolResult;
import org.eclipse.swtbot.swt.finder.results.Result;
import org.eclipse.swtbot.swt.finder.widgets.AbstractSWTBotControl;
import org.eclipse.ui.internal.views.properties.tabbed.view.TabbedPropertyList;
import org.eclipse.ui.internal.views.properties.tabbed.view.TabbedPropertyList.ListElement;
import org.eclipse.ui.views.properties.tabbed.ITabItem;
import org.key_project.util.java.ObjectUtil;

/**
 * This represents a {@link TabbedPropertyList} widget.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SWTBotTabbedPropertyList extends AbstractSWTBotControl<TabbedPropertyList> {
   /**
    * Constructor.
    * @param w the widget.
    * @throws WidgetNotFoundException if the widget is <code>null</code> or widget has been disposed.
    */
   public SWTBotTabbedPropertyList(TabbedPropertyList w) throws WidgetNotFoundException {
      super(w);
   }
   
   /**
    * Factory method.
    * @param bot The {@link SWTBot} to use.
    * @return The instantiated {@link SWTBotTabbedPropertyList}.
    * @throws WidgetNotFoundException If no widget is available.
    */
   public static SWTBotTabbedPropertyList tabbedPropertyList(SWTBot bot) throws WidgetNotFoundException {
      TabbedPropertyList w = (TabbedPropertyList)bot.widget(WidgetMatcherFactory.widgetOfType(TabbedPropertyList.class));
      if (w != null) {
         return new SWTBotTabbedPropertyList(w);
      }
      else{
         throw new WidgetNotFoundException("Can't find TabbedPropertyList.");
      }
   }
   
   /**
    * Checks if a tab with the given text is available.
    * @param text The tab text.
    * @return {@code true} tab available, {@code false} tab not available.
    */
   public boolean hasTabItem(final String text) {
      return syncExec(new BoolResult() {
         @Override
         public Boolean run() {
            int i = 0;
            Object element;
            boolean found = false;
            while (!found && (element = widget.getElementAt(i)) != null) {
               Assert.isTrue(element instanceof ListElement);
               ListElement le = (ListElement)element;
               if (ObjectUtil.equals(text, le.getTabItem().getText())) {
                  found = true;
               }
               else {
                  i++;
               }
            }
            return Boolean.valueOf(found);
         }
      });
   }
   
   /**
    * Selects a tab with the given text.
    * @param text The text of the tab to select.
    * @return {@code true} tab selected successfully, {@code false} selection failed.
    */
   public boolean selectTabItem(final String text) {
      return syncExec(new BoolResult() {
         @Override
         public Boolean run() {
            try {
               int i = 0;
               Object element;
               boolean found = false;
               while (!found && (element = widget.getElementAt(i)) != null) {
                  Assert.isTrue(element instanceof ListElement);
                  ListElement le = (ListElement)element;
                  if (ObjectUtil.equals(text, le.getTabItem().getText())) {
                     found = true;
                  }
                  else {
                     i++;
                  }
               }
               if (found) {
                  ObjectUtil.invoke(widget, ObjectUtil.findMethod(TabbedPropertyList.class, "select", int.class), i);
                  widget.redraw();
                  return Boolean.valueOf(i == widget.getSelectionIndex());
               }
               else {
                  return Boolean.FALSE;
               }
            }
            catch (Exception e) {
               throw new RuntimeException(e);
            }
         }
      });
   }
   
   /**
    * Returns all available {@link ITabItem}s.
    * @return The available {@link ITabItem}s.
    */
   public List<ITabItem> getTabItems() {
      return syncExec(new Result<List<ITabItem>>() {
         @Override
         public List<ITabItem> run() {
            List<ITabItem> result = new LinkedList<ITabItem>();
            int i = 0;
            Object element;
            while ((element = widget.getElementAt(i)) != null) {
               Assert.isTrue(element instanceof ListElement);
               ListElement le = (ListElement)element;
               result.add(le.getTabItem());
               i++;
            }
            return result;
         }
      });
   }
}