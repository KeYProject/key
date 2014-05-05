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

package org.key_project.swtbot.swing.bot.finder.waits;

import java.awt.Component;

import org.eclipse.swtbot.swt.finder.utils.internal.Assert;
import org.eclipse.swtbot.swt.finder.waits.DefaultCondition;
import org.eclipse.swtbot.swt.finder.waits.ICondition;
import org.key_project.swtbot.swing.bot.AbstractSwingBotComponent;
import org.key_project.swtbot.swing.bot.SwingBotJDialog;


/**
 * <p>
 * An {@link ICondition} that checks if a {@link Component} is closed.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.waits.ShellCloses}.
 * </p>
 * @author Martin Hentschel
 */
class ComponentCloses extends DefaultCondition {
   /**
    * The {@link SwingBotJDialog} to check.
    */
   private final AbstractSwingBotComponent<? extends Component> component;

   /**
    * Constructor.
    * @param component The {@link AbstractSwingBotComponent} to check.
    */
   ComponentCloses(AbstractSwingBotComponent<? extends Component> component) {
      Assert.isNotNull(component, "The Component was null");
      this.component = component;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFailureMessage() {
      return "The Component " + component + " did not close.";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test() throws Exception {
      return !component.isVisible();
   }
}