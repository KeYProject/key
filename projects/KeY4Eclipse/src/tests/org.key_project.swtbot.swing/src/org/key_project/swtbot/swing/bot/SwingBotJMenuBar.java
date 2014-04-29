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

package org.key_project.swtbot.swing.bot;

import java.awt.Component;
import java.util.List;

import javax.swing.JMenu;
import javax.swing.JMenuBar;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.hamcrest.Matcher;
import org.key_project.swtbot.swing.bot.finder.finders.Finder;
import org.key_project.swtbot.swing.finder.matchers.ComponentMatcherFactory;


/**
 * <p>
 * This represents a {@link JMenuBar} {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link SWTBotMenu}.
 * </p>
 * @author Martin Hentschel
 */
public class SwingBotJMenuBar extends AbstractSwingBotComponent<JMenuBar> {
   /**
    * The {@link Finder} that is used to find child menus and menu items.
    */
   private final Finder finder;

   /**
    * Constructs an instance of this object with the given {@link JMenuBar}.
    * @param component The given {@link JMenuBar}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */      
   public SwingBotJMenuBar(Finder finder, JMenuBar component) throws WidgetNotFoundException {
      super(component);
      this.finder = finder;
   }
   
   /**
    * Gets the {@link JMenu} matching the given title.
    * @param title The name of the {@link JMenu} that is to be found
    * @return The first menu that matches the menuName
    * @throws WidgetNotFoundException If the {@link Component} is not found.
    */
   @SuppressWarnings({ "rawtypes", "unchecked" })
   public SwingBotJMenu menu(String title) throws WidgetNotFoundException {
      Matcher withText = ComponentMatcherFactory.allOf(ComponentMatcherFactory.componentOfType(JMenu.class), ComponentMatcherFactory.withText(title));
      List<JMenu> menus = finder.findMenus(component, withText, true);
      if (!menus.isEmpty()) 
         return new SwingBotJMenu(finder, menus.get(0));
      else {
         return null;
      }
   }
}