/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.swtbot.swing.bot.finder.finders;

import java.awt.Component;
import java.util.List;

import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JMenuBar;

import org.eclipse.swtbot.swt.finder.finders.ChildrenControlFinder;
import org.hamcrest.Matcher;

/**
 * <p>
 * Finds {@link Component}s matching a particular matcher in the given parent {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link ChildrenControlFinder}.
 * </p>
 * @author Martin Hentschel
 */
public class ChildrenComponentFinder extends ComponentFinder {
   /**
    * The parent {@link Component} to begin searching for children.
    */
   protected final Component parentComponent;

   /**
    * Constructs a child component finder component using the given parent {@link Component} as its starting point.
    * @param parentComponent The parent widget in which controls should be found.
    */
   public ChildrenComponentFinder(Component parentComponent) {
      super();
      this.parentComponent = parentComponent;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public <T extends Component> List<T> findComponents(Matcher<T> matcher) {
      return findComponents(parentComponent, matcher, true);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public JMenuBar findJMenuBar() {
      if (parentComponent instanceof JFrame) {
         return ((JFrame)parentComponent).getJMenuBar();
      }
      else if (parentComponent instanceof JDialog) {
         return ((JDialog)parentComponent).getJMenuBar();
      }
      else {
         throw null;
      }
   }
}
