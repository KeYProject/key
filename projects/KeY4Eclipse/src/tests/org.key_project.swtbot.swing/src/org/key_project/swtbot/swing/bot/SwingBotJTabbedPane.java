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

package org.key_project.swtbot.swing.bot;

import java.awt.Component;

import javax.swing.JTabbedPane;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTabItem;

/**
 * <p>
 * This represents a {@link JTabbedPane} {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link SWTBotTabItem}.
 * </p>
 * @author Martin Hentschel
 */
public class SwingBotJTabbedPane extends AbstractSwingBotComponent<JTabbedPane> {
   /**
    * Constructs an instance of this object with the given {@link JTabbedPane}.
    * @param component The given {@link JTabbedPane}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */      
   public SwingBotJTabbedPane(JTabbedPane component) throws WidgetNotFoundException {
      super(component);
   }
   
   /**
    * Selects the tab at the given index.
    * @param index The index to select.
    * @return A created {@link AbstractSwingBotComponent} to handle the selected tab {@link Component}.
    */
   public AbstractSwingBotComponent<? extends Component> select(int index) {
      component.setSelectedIndex(index);
      Component selectedComponent = component.getComponentAt(index);
      return SwingBot.createBotComponent(bot().getFinder(), selectedComponent);
   }

   /**
    * Returns the title at the defined index.
    * @param index The index.
    * @return The title at that index.
    */
   public String getTitleAt(int index) {
      return component.getTitleAt(index);
   }

   /**
    * Returns the first tab that has the given title.
    * @param title The title.
    * @return The index of the first tab with the title or {@code -1} if no tab has the title.
    */
   public int indexOfTitle(String title) {
      return component.indexOfTab(title);
   }
}
