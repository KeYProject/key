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

package org.key_project.swtbot.swing.bot.finder.finders;

import java.awt.Component;
import java.awt.Window;
import java.util.List;

import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;

import org.hamcrest.Matcher;

/**
 * <p>
 * A wrapper around {@link ComponentFinder} and {@link MenuFinder} that delegates to either of them.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.finders.Finder}.
 * </p>
 * @author Martin Hentschel
 */
public class Finder extends org.eclipse.swtbot.swt.finder.finders.Finder {
   /**
    * The {@link ComponentFinder} to use.
    */
   private final ComponentFinder swingComponentFinder;

   /**
    *  The {@link MenuFinder} to use.
    */
   private final MenuFinder swingMenuFinder;
   
   /**
    * Constructs a default instance.
    */
   public Finder() {
      this(new ComponentFinder(), new MenuFinder());
   }
   
   /**
    * Constructs the finder with the given control and menu finder.
    * @param controlFinder The finder that finds controls.
    * @param menuFinder The finder that finds menus.
    */
   public Finder(org.eclipse.swtbot.swt.finder.finders.ControlFinder controlFinder, org.eclipse.swtbot.swt.finder.finders.MenuFinder menuFinder) {
      super(controlFinder, menuFinder);
      this.swingComponentFinder = new ComponentFinder();
      this.swingMenuFinder = new MenuFinder();
   }

   /**
    * Establishes the finder from an existing finder (control finder only) and the given new menu finder.
    * @param finder The finder
    * @param menuFinder The finder that finds menus.
    */
   public Finder(org.eclipse.swtbot.swt.finder.finders.Finder finder, org.eclipse.swtbot.swt.finder.finders.MenuFinder menuFinder) {
      super(finder, menuFinder);
      this.swingComponentFinder = new ComponentFinder();
      this.swingMenuFinder = new MenuFinder();
   }

   /**
    * Constructs the finder with the {@link ComponentFinder} and {@link MenuFinder}.
    * @param swingComponentFinder The {@link ComponentFinder} that finds {@link Component}s.
    * @param swingMenuFinder The {@link MenuFinder} that finds {@link JMenu}s and {@link JMenuItem}s.
    */
   public Finder(ComponentFinder swingComponentFinder, MenuFinder swingMenuFinder) {
      super(new org.eclipse.swtbot.swt.finder.finders.ControlFinder(), new org.eclipse.swtbot.swt.finder.finders.MenuFinder());
      this.swingComponentFinder = swingComponentFinder;
      this.swingMenuFinder = swingMenuFinder;
   }
   
   /**
    * Finds all the {@link JMenuItem}s in the given menu matching the given matcher.
    * @param menu The menu
    * @param matcher The matcher that can match menus and menu items.
    * @return All menu items in the specified menu that match the matcher.
    * @see MenuFinder#findItems(JMenu, Matcher)
    */
   public List<JMenuItem> findItems(JMenu menu, final Matcher<JMenuItem> matcher) {
      return swingMenuFinder.findItems(menu, matcher);
   }
   
   /**
    * Finds all the {@link JMenu}s in the given menu bar matching the given matcher. If recursive is set, it will attempt to
    * find the controls recursively in each of the menus it that is found.
    * @param bar The menu bar
    * @param matcher The matcher that can match menus and menu items.
    * @param recursive If set to true, will find sub-menus as well.
    * @return All menus in the specified menu bar that match the matcher.
    * @see MenuFinder#findMenus(JMenuBar, Matcher, boolean)
    */
   public List<JMenu> findMenus(JMenuBar bar, Matcher<JMenu> matcher, boolean recursive) {
      return swingMenuFinder.findMenus(bar, matcher, recursive);
   }
   
   /**
    * Finds the {@link Component}s in the active shell matching the given matcher.
    * @param <T> The type of the found {@link Component}s.
    * @param matcher The matcher used to find {@link Component}s in the active {@link Window}.
    * @return All controls in the active {@link Window} that the matcher matches.
    * @see ComponentFinder#findComponents(Matcher)
    */
   public <T extends Component> List<T> findComponents(final Matcher<T> matcher) {
      return swingComponentFinder.findComponents(matcher);
   }
   
   /**
    * Finds the {@link JMenuBar} of the active {@link Window}.
    * @return The {@link JMenuBar} of the active {@link Window} or {@code null} if it has no one.
    * @see ComponentFinder#findJMenuBar()
    */
   public JMenuBar findJMenuBar() {
      return swingComponentFinder.findJMenuBar();
   }
}