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

package org.key_project.swtbot.swing.bot;

import java.awt.Component;

import javax.swing.JRadioButton;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;

/**
 * <p>
 * This represents a {@link JRadioButton} {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link SWTBotButton}.
 * </p>
 * @author Martin Hentschel
 */
public class SwingBotJRadioButton extends AbstractSwingBotButtonComponent<JRadioButton> {
   /**
    * Constructs an instance of this object with the given {@link JRadioButton}.
    * @param component The given {@link JRadioButton}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */
   public SwingBotJRadioButton(JRadioButton component) throws WidgetNotFoundException {
      super(component);
   }
}