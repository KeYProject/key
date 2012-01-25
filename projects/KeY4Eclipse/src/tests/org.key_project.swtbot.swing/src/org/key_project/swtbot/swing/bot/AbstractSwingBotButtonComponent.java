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

import javax.swing.AbstractButton;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.utils.MessageFormat;
import org.eclipse.swtbot.swt.finder.widgets.AbstractSWTBot;

/**
 * <p>
 * Helper to find Swing {@link AbstractButton}s and perform operations on them.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link AbstractSWTBot}.
 * </p>
 * @author Martin Hentschel
 */
public class AbstractSwingBotButtonComponent<T extends AbstractButton> extends AbstractSwingBotComponent<T> {
   /**
    * Constructs a new instance with the given {@link Component}.
    * @param component The {@link Component}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */
   public AbstractSwingBotButtonComponent(T component) throws WidgetNotFoundException {
      super(component);
   }

   /**
    * Executes an asynchronous click on the button.
    * @return The button on that was clicked.
    */
   public AbstractSwingBotButtonComponent<T> click() {
      waitForEnabled();
      Thread x = new Thread() {
         @Override
         public void run() {
            clickAndWait();
         }
      };
      x.start();
      try {
         Thread.sleep(100);
      }
      catch (InterruptedException e) {
      }
      return this;
   }

   /**
    * Executes an synchronous click on the button.
    * @return The button on that was clicked.
    */
   public AbstractSwingBotButtonComponent<T> clickAndWait() {
      log.debug(MessageFormat.format("Clicking on {0}", this));
      component.doClick();
      log.debug(MessageFormat.format("Clicked on {0}", this));
      return this;
   }
}