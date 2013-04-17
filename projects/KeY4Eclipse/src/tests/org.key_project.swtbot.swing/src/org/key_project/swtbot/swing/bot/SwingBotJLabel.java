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

import javax.swing.JLabel;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotLabel;
import org.key_project.swtbot.swing.util.AbstractRunnableWithResult;
import org.key_project.swtbot.swing.util.IRunnableWithResult;
import org.key_project.swtbot.swing.util.SaveSwingUtil;

/**
 * <p>
 * This represents a {@link JLabel} {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link SWTBotLabel}.
 * </p>
 * @author Martin Hentschel
 */
public class SwingBotJLabel extends AbstractSwingBotComponent<JLabel> {
   /**
    * Constructs an instance of this object with the given {@link JLabel}.
    * @param component The given {@link JLabel}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */
   public SwingBotJLabel(JLabel component) throws WidgetNotFoundException {
      super(component);
   }
   
   /**
    * Returns the shown text.
    * @return The shown text.
    */
   public String getText() {
       IRunnableWithResult<String> run = new AbstractRunnableWithResult<String>() {
           @Override
           public void run() {
               setResult(component.getText());
           }
       };
       SaveSwingUtil.invokeAndWait(run);
       return run.getResult();
   }
}