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

import javax.swing.JFrame;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;

/**
 * <p>
 * This represents a {@link JFrame} {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link SWTBotShell}.
 * </p>
 * @author Martin Hentschel
 */
public class SwingBotJFrame extends AbstractSwingBotComponent<JFrame> {
   /**
    * Constructs an instance of this object with the given {@link JFrame}.
    * @param component The given {@link JFrame}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */   
   public SwingBotJFrame(JFrame component) throws WidgetNotFoundException {
      super(component);
   }
   
   /**
    * Closes the {@link JFrame}.
    */
   public void close() {
      component.setVisible(false);
   }
   
   /**
    * Checks if the {@link JFrame} is open.
    * @return {@code true} if the shell is visible, {@code false} otherwise.
    * @see JFrame#isVisible()
    */
   public boolean isOpen() {
      return component.isVisible();
   }
   
   /**
    * Checks if the {@link JFrame} is active.
    * @return {@code true} if the shell is active, {@code false} otherwise.
    * @see JFrame#isActive()
    */
   public boolean isActive() {
      return component.isActive();
   }
}
