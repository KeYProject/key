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

import javax.swing.JDialog;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.key_project.swtbot.swing.util.AbstractRunnableWithResult;
import org.key_project.swtbot.swing.util.IRunnableWithResult;
import org.key_project.swtbot.swing.util.SaveSwingUtil;

/**
 * <p>
 * This represents a {@link JDialog} {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link SWTBotShell}.
 * </p>
 * @author Martin Hentschel
 */
public class SwingBotJDialog extends AbstractSwingBotComponent<JDialog> {
   /**
    * Constructs an instance of this object with the given {@link JDialog}.
    * @param component The given {@link JDialog}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */
   public SwingBotJDialog(JDialog component) throws WidgetNotFoundException {
      super(component);
   }
   
   /**
    * Closes the {@link JDialog}.
    */
   public void close() {
      SaveSwingUtil.invokeAndWait(new Runnable() {
         @Override
         public void run() {
            component.setVisible(false);
         }
      });
   }
   
   /**
    * Checks if the {@link JDialog} is open.
    * @return {@code true} if the shell is visible, {@code false} otherwise.
    * @see JDialog#isVisible()
    */
   public boolean isOpen() {
      IRunnableWithResult<Boolean> run = new AbstractRunnableWithResult<Boolean>() {
         @Override
         public void run() {
            setResult(component.isVisible());
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      return run.getResult() != null && run.getResult().booleanValue();
   }
   
   /**
    * Checks if the {@link JDialog} is active.
    * @return {@code true} if the shell is active, {@code false} otherwise.
    * @see JDialog#isActive()
    */
   public boolean isActive() {
      IRunnableWithResult<Boolean> run = new AbstractRunnableWithResult<Boolean>() {
         @Override
         public void run() {
            setResult(component.isActive());
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      return run.getResult() != null && run.getResult().booleanValue();
   }
}