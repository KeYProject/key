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
import java.awt.Frame;
import java.awt.Window;

import javax.swing.JList;
import javax.swing.JTree;

import org.eclipse.swtbot.swt.finder.waits.ICondition;
import org.eclipse.swtbot.swt.finder.waits.WaitForObjectCondition;
import org.hamcrest.Matcher;
import org.key_project.swtbot.swing.bot.AbstractSwingBotComponent;
import org.key_project.swtbot.swing.bot.SwingBot;
import org.key_project.swtbot.swing.bot.SwingBotJList;
import org.key_project.swtbot.swing.bot.SwingBotJTree;


/**
 * <p>
 * This is a factory class to create some conditions provided with {@link SwingBot}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.waits.Conditions}.
 * </p>
 * @author Martin Hentschel
 */
public abstract class Conditions {
   /**
    * Waits for a {@link Frame}.
    * @param <T> The result type.
    * @param matcher The matcher to use.
    * @return The expected {@link Frame}.
    */
   public static <T extends Frame> WaitForObjectCondition<T> waitForFrame(Matcher<T> matcher) {
      return new WaitForFrame<T>(matcher);
   }

   /**
    * Waits for a {@link Window}.
    * @param <T> The result type.
    * @param matcher The matcher to use.
    * @return The expected {@link Window}.
    */
   public static <T extends Window> WaitForObjectCondition<T> waitForWindow(Matcher<T> matcher) {
      return new WaitForWindow<T>(matcher);
   }
   
   /**
    * Waits for a {@link Component}.
    * @param <T> The result type.
    * @param matcher The matcher to use.
    * @return The expected {@link Component}.
    */
   public static <T extends Component> WaitForObjectCondition<T> waitForComponent(Matcher<T> matcher) {
      return new WaitForComponent<T>(matcher);
   }
   
   /**
    * Checks if the {@link Component} is enabled. 
    * @param component The {@link Component} to check.
    * @return The created {@link ICondition}.
    */
   public static ICondition componentIsEnabled(AbstractSwingBotComponent<? extends Component> component){
      return new ComponentIsEnabledCondition(component);
   }
   
   /**
    * Checks if the {@link Component} is closed. 
    * @param component The {@link Component} to check.
    * @return The created {@link ICondition}.
    */
   public static ICondition componentCloses(AbstractSwingBotComponent<? extends Component> component) {
      return new ComponentCloses(component);
   }

   /**
    * Checks if the {@link JTree} has a selection.
    * @param tree The {@link JTree} to check.
    * @return The created {@link ICondition}.
    */
   public static ICondition hasSelection(SwingBotJTree tree) {
      return new HasSelectionCondition<JTree>(tree);
   }

   /**
    * Checks if the {@link JList} has a selection.
    * @param list The {@link JList} to check.
    * @return The created {@link ICondition}.
    */   
   public static ICondition hasSelection(SwingBotJList list) {
      return new HasSelectionCondition<JList>(list);
   }
}