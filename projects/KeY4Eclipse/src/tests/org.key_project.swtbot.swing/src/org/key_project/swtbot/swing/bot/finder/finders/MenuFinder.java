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

package org.key_project.swtbot.swing.bot.finder.finders;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;

import org.hamcrest.Matcher;
import org.key_project.swtbot.swing.util.AbstractRunnableWithResult;
import org.key_project.swtbot.swing.util.IRunnableWithResult;
import org.key_project.swtbot.swing.util.SaveSwingUtil;

/**
 * <p>
 * 
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.finders.MenuFinder}.
 * </p>
 * @author Martin Hentschel
 */
public class MenuFinder {
   /**
    * Finds all the {@link JMenu}s in the given menu bar matching the given matcher. If recursive is set, it will attempt to
    * find the controls recursively in each of the menus it that is found.
    * @param bar The menu bar
    * @param matcher The matcher that can match menus and menu items.
    * @param recursive If set to true, will find sub-menus as well.
    * @return All menus in the specified menu bar that match the matcher.
    */
   public List<JMenu> findMenus(JMenuBar bar, Matcher<JMenu> matcher, boolean recursive) {
      return findMenusInternal(bar, matcher, recursive);
   }

   /**
    * Finds all the {@link JMenu}s in the given menu bar matching the given matcher. If recursive is set, it will attempt to
    * find the controls recursively in each of the menus it that is found.
    * @param bar The menu bar
    * @param matcher The matcher that can match menus and menu items.
    * @param recursive If set to true, will find sub-menus as well.
    * @return All menus in the specified menu bar that match the matcher.
    */
   private List<JMenu> findMenusInternal(final JMenuBar bar, 
                                         final Matcher<JMenu> matcher, 
                                         final boolean recursive) {
      IRunnableWithResult<List<JMenu>> run = new AbstractRunnableWithResult<List<JMenu>>() {
         @Override
         public void run() {
            LinkedHashSet<JMenu> result = new LinkedHashSet<JMenu>();
            if (bar != null) {
               for (int i = 0; i < bar.getMenuCount(); i++) {
                  JMenu menu = bar.getMenu(i);
                  if (matcher.matches(menu))
                     result.add(menu);
                  if (recursive)
                     result.addAll(findMenusInternal(menu, matcher, recursive));
               }
            }
            setResult(new ArrayList<JMenu>(result));
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      return run.getResult();
   }

   /**
    * Finds all the {@link JMenu}s in the given menu matching the given matcher. If recursive is set, it will attempt to
    * find the controls recursively in each of the menus it that is found.
    * @param menu The menu
    * @param matcher The matcher that can match menus and menu items.
    * @param recursive If set to true, will find sub-menus as well.
    * @return All menus in the specified menu that match the matcher.
    */
   private List<JMenu> findMenusInternal(final JMenu menu, 
                                         final Matcher<JMenu> matcher, 
                                         final boolean recursive) {
      IRunnableWithResult<List<JMenu>> run = new AbstractRunnableWithResult<List<JMenu>>() {
         @Override
         public void run() {
            LinkedHashSet<JMenu> result = new LinkedHashSet<JMenu>();
            if (menu != null) {
               for (int i = 0; i < menu.getItemCount(); i++) {
                  JMenuItem item = menu.getItem(i);
                  if (item instanceof JMenu) {
                     JMenu childMenu = (JMenu)item;
                     if (matcher.matches(childMenu))
                        result.add(childMenu);
                     if (recursive)
                        result.addAll(findMenusInternal(childMenu, matcher, recursive));
                  }
               }
            }
            setResult(new ArrayList<JMenu>(result));
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      return run.getResult();
   }
   
   /**
    * Finds all the {@link JMenuItem}s in the given menu matching the given matcher.
    * @param menu The menu
    * @param matcher The matcher that can match menus and menu items.
    * @return All menu items in the specified menu that match the matcher.
    */
   public List<JMenuItem> findItems(JMenu menu, final Matcher<JMenuItem> matcher) {
      return findItemsInternal(menu, matcher);
   }

   /**
    * Finds all the {@link JMenuItem}s in the given menu matching the given matcher.
    * @param menu The menu
    * @param matcher The matcher that can match menus and menu items.
    * @return All menu items in the specified menu that match the matcher.
    */
   private List<JMenuItem> findItemsInternal(final JMenu menu, 
                                             final Matcher<JMenuItem> matcher) {
      IRunnableWithResult<List<JMenuItem>> run = new AbstractRunnableWithResult<List<JMenuItem>>() {
         @Override
         public void run() {
            LinkedHashSet<JMenuItem> result = new LinkedHashSet<JMenuItem>();
            if (menu != null) {
               for (int i = 0; i < menu.getItemCount(); i++) {
                  JMenuItem item = menu.getItem(i);
                  if (matcher.matches(item))
                     result.add(item);
               }
            }
            setResult(new ArrayList<JMenuItem>(result));
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      return run.getResult();
   }
}