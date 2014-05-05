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

import org.eclipse.swtbot.swt.finder.waits.DefaultCondition;
import org.eclipse.swtbot.swt.finder.waits.ICondition;
import org.key_project.swtbot.swing.bot.AbstractSwingBotComponent;
import org.key_project.swtbot.swing.bot.SwingBotJList;
import org.key_project.swtbot.swing.bot.SwingBotJTree;


/**
 * <p>
 * An {@link ICondition} that checks if a {@link AbstractSwingBotComponent} has selected elements.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.waits.WidgetIsEnabledCondition}.
 * </p>
 * @author Martin Hentschel
 */
class HasSelectionCondition<T extends Component> extends DefaultCondition {
   /**
    * The {@link SwingBotJTree} to check.
    */
   private final AbstractSwingBotComponent<T> component;

   /**
    * Constructor.
    * @param component The {@link AbstractSwingBotComponent} to check.
    */
   HasSelectionCondition(AbstractSwingBotComponent<T> component) {
      this.component = component;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test() throws Exception {
      if (component instanceof SwingBotJTree) {
         return ((SwingBotJTree)component).getSelectedObjects().length >= 1;
      }
      else if (component instanceof SwingBotJList) {
         return ((SwingBotJList)component).getSelectedObjects().length >= 1;
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFailureMessage() {
      return "The component " + component + " has no selection.";
   }
}