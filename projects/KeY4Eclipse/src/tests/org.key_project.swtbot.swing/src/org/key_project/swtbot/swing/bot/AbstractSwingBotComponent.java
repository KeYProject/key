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

import javax.swing.JDialog;

import org.apache.log4j.Logger;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.AbstractSWTBot;
import org.key_project.swtbot.swing.bot.finder.waits.Conditions;


/**
 * <p>
 * Helper to find Swing {@link Component}s and perform operations on them.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link AbstractSWTBot}.
 * </p>
 * @author Martin Hentschel
 */
public class AbstractSwingBotComponent<T extends Component> {
   /**
    * With great power comes great responsibility, use carefully.
    */
   public final T component;
   
   /**
    * The logger.
    */
   protected final Logger log;

   /**
    * Constructs a new instance with the given {@link Component}.
    * @param component The {@link Component}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */
   public AbstractSwingBotComponent(T component) throws WidgetNotFoundException {
      super();
      if (component == null) {
         throw new WidgetNotFoundException("The component was null.");
      }
      this.component = component;
      this.log = Logger.getLogger(getClass());;
   }
   
   /**
    * Gets if the object's {@link Component} is enabled.
    * @return {@code true} if the widget is enabled.
    * @see Component#isEnabled()
    */
   public boolean isEnabled() {
      return component.isEnabled();
   }
   
   /**
    * Wait until the {@link Component} is enabled.
    */
   protected void waitForEnabled() {
      new SwingBot().waitUntil(Conditions.componentIsEnabled(this));
   }
   
   /**
    * Returns a {@link SwingBot} instance that matches the contents of this {@link JDialog}.
    * @return The created {@link SwingBot}.
    */
   public SwingBot bot() {
      return new SwingBot(component);
   }
}