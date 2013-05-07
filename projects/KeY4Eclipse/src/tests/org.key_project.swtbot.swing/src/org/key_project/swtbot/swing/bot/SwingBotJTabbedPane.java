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

import javax.swing.JTabbedPane;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTabItem;
import org.key_project.swtbot.swing.util.AbstractRunnableWithResult;
import org.key_project.swtbot.swing.util.IRunnableWithResult;
import org.key_project.swtbot.swing.util.SaveSwingUtil;

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
   public AbstractSwingBotComponent<? extends Component> select(final int index) {
      IRunnableWithResult<Component> run = new AbstractRunnableWithResult<Component>() {
        @Override
        public void run() {
           component.setSelectedIndex(index);
           Component selectedComponent = component.getComponentAt(index);
           setResult(selectedComponent);
        }
      };
      SaveSwingUtil.invokeAndWait(run);
      Component selectedComponent = run.getResult();
      return SwingBot.createBotComponent(bot().getFinder(), selectedComponent);
   }

   /**
    * Returns the title at the defined index.
    * @param index The index.
    * @return The title at that index.
    */
   public String getTitleAt(final int index) {
      IRunnableWithResult<String> run = new AbstractRunnableWithResult<String>() {
         @Override
         public void run() {
            setResult(component.getTitleAt(index));
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      return run.getResult();
   }

   /**
    * Returns the first tab that has the given title.
    * @param title The title.
    * @return The index of the first tab with the title or {@code -1} if no tab has the title.
    */
   public int indexOfTitle(final String title) {
      IRunnableWithResult<Integer> run = new AbstractRunnableWithResult<Integer>() {
         @Override
         public void run() {
            setResult(component.indexOfTab(title));
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      return run.getResult();
   }
}