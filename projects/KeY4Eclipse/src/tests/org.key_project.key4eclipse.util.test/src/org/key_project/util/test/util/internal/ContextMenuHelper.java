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

package org.key_project.util.test.util.internal;

import static org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory.withMnemonic;
import static org.hamcrest.Matchers.allOf;
import static org.hamcrest.Matchers.instanceOf;

import java.util.Arrays;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swt.widgets.Widget;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable;
import org.eclipse.swtbot.swt.finder.results.VoidResult;
import org.eclipse.swtbot.swt.finder.results.WidgetResult;
import org.eclipse.swtbot.swt.finder.widgets.AbstractSWTBot;
import org.hamcrest.Matcher;

// see http://www.eclipse.org/forums/index.php/t/11863/
public class ContextMenuHelper {
   /**
    * Clicks the context menu matching the text.
    * 
    * @param text
    *            the text on the context menu.
    * @throws WidgetNotFoundException
    *             if the widget is not found.
    */
   public static void clickContextMenu(final AbstractSWTBot<?> bot, 
                                       final int x, 
                                       final int y, 
                                       final String... texts) {

      // show
      final MenuItem menuItem = UIThreadRunnable
            .syncExec(new WidgetResult<MenuItem>() {
               public MenuItem run() {
                  MenuItem menuItem = null;
                  Control control = (Control) bot.widget;
                  
                  //MenuDetectEvent added by Stefan Schaefer
                  Event event = createEvent(null, x, y);
                  control.notifyListeners(SWT.MenuDetect, event);
                  if (!event.doit) {
                     return null;
                  }
                  
                  Menu menu = control.getMenu();
                  for (String text : texts) {
                     @SuppressWarnings("unchecked")
                     Matcher<?> matcher = allOf(
                           instanceOf(MenuItem.class),
                           withMnemonic(text));
                     menuItem = show(menu, x, y, matcher);
                     if (menuItem != null) {
                        menu = menuItem.getMenu();
                     } else {
                        hide(menu, x, y);
                        break;
                     }
                  }

                  return menuItem;
               }
            });
      if (menuItem == null) {
         throw new WidgetNotFoundException("Could not find menu: "
               + Arrays.asList(texts));
      }

      // click
      click(menuItem, x, y);

      // hide
      UIThreadRunnable.syncExec(new VoidResult() {
         public void run() {
            hide(menuItem.getParent(), x, y);
         }
      });
   }

   private static MenuItem show(final Menu menu, final int x, final int y, final Matcher<?> matcher) {
      if (menu != null) {
         menu.notifyListeners(SWT.Show, createEvent(null, x, y));
         MenuItem[] items = menu.getItems();
         for (final MenuItem menuItem : items) {
            if (matcher.matches(menuItem)) {
               return menuItem;
            }
         }
         menu.notifyListeners(SWT.Hide, createEvent(null, x, y));
      }
      return null;
   }

   private static void click(final MenuItem menuItem, final int x, final int y) {
      final Event event = createEvent(menuItem, x, y);
      event.type = SWT.Selection;

      UIThreadRunnable.asyncExec(menuItem.getDisplay(), new VoidResult() {
         public void run() {
            menuItem.notifyListeners(SWT.Selection, event);
         }
      });
   }

   private static void hide(final Menu menu, final int x, final int y) {
      menu.notifyListeners(SWT.Hide, createEvent(menu, x, y));
      if (menu.getParentMenu() != null) {
         hide(menu.getParentMenu(), x, y);
      }
   }
   
   private static Event createEvent(Widget widget, int x, int y) {
      Event event = new Event();
      event.time = (int) System.currentTimeMillis();
      event.widget = widget;
      event.display = widget != null ? widget.getDisplay() : Display.getCurrent();
      return event;
   }
}