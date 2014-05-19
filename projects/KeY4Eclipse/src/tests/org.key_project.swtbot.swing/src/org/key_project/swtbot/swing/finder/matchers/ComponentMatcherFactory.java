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

package org.key_project.swtbot.swing.finder.matchers;

import java.awt.Component;

import javax.swing.JTree;
import javax.swing.tree.TreeModel;

import org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory;
import org.hamcrest.Matcher;
import org.key_project.swtbot.swing.bot.SwingBot;


/**
 * <p>
 * This is a factory class to create some matchers provided with {@link SwingBot}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link WidgetMatcherFactory}.
 * </p>
 * @author Martin Hentschel
 */
public abstract class ComponentMatcherFactory {
   /**
    * Matches a widget that has the specified exact title.
    * @param <T> The expected {@link Component} type.
    * @param title the label.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> withTitle(String title) {
      return WithTitle.withTitle(title);
   }

   /**
    * Matches a widget that has the specified title, ignoring case considerations.
    * @param <T> The expected {@link Component} type.
    * @param title the label.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> withTitleIgnoringCase(String title) {
      return WithTitle.withTitleIgnoringCase(title);
   }

   /**
    * Matches a widget that starts with the specified title.
    * @param <T> The expected {@link Component} type.
    * @param title the label.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> withStartingTitle(String title) {
      return WithStartingTitle.withStartingTitle(title);
   }

   /**
    * Matches a widget that starts with the specified title, ignoring case considerations.
    * @param <T> The expected {@link Component} type.
    * @param title the label.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> withStartingTitleIgnoringCase(String title) {
      return WithStartingTitle.withStartingTitleIgnoringCase(title);
   }

   /**
    * Matches a widget that has the specified exact text.
    * @param <T> The expected {@link Component} type.
    * @param title the label.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> withText(String title) {
      return WithText.withText(title);
   }

   /**
    * Matches a widget that has the specified text, ignoring case considerations.
    * @param <T> The expected {@link Component} type.
    * @param title the label.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> withTextIgnoringCase(String title) {
      return WithText.withTextIgnoringCase(title);
   }

   /**
    * Matches a widget that starts with the specified text.
    * @param <T> The expected {@link Component} type.
    * @param title the label.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> withStartingText(String title) {
      return WithStartingText.withStartingText(title);
   }

   /**
    * Matches a widget that starts with the specified text, ignoring case considerations.
    * @param <T> The expected {@link Component} type.
    * @param title the label.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> withStartingTextIgnoringCase(String title) {
      return WithStartingText.withStartingTextIgnoringCase(title);
   }

   /**
    * Matches a widget that has the specified exact tool tip.
    * @param <T> The expected {@link Component} type.
    * @param tooltip the tool tip.
    * @return a matcher.
    */   
   public static <T extends Component> Matcher<T> withToolTipText(String tooltip) {
      return WithToolTipText.withToolTipText(tooltip);
   }

   /**
    * Matches a widget that has the specified tool tip, ignoring case considerations.
    * @param <T> The expected {@link Component} type.
    * @param tooltip the tool tip.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> withToolTipTextIgnoringCase(String tooltip) {
      return WithToolTipText.withToolTipTextIgnoringCase(tooltip);
   }

   /**
    * Evaluates to true only if ALL of the passed in matchers evaluate to true.
    * @param <T> The expected {@link Component} type.
    * @param matchers he {@link Matcher} to use as children.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> allOf(Matcher<? extends T>... matchers) {
      return AllOf.allOf(matchers);
   }

   /**
    * Matches a {@link Component} that has the specified type.
    * @param <T> The expected {@link Component} type.
    * @param type the type of the {@link Component}.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> componentOfType(java.lang.Class<T> type) {
      return ComponentOfType.componentOfType(type);
   }

   /**
    * Matches a {@link Component} that is a {@link JTree} and has a model of the specified type.
    * @param treeModelType The type of the {@link TreeModel}.
    * @return a matcher.
    */   
   public static Matcher<? extends JTree> treeModelOfType(Class<? extends TreeModel> treeModelType) {
      return TreeModelOfType.treeModelOfType(treeModelType);
   }

   /**
    * Matches a widget that is visible.
    * @param <T> The type of the expected {@link Component}s.
    * @param expectedVisibility The expected visibility.
    * @return a matcher.
    */
   public static <T extends Component> Matcher<T> componentVisibility(boolean expectedVisibility) {
      return ComponentVisibility.componentVisibility(expectedVisibility);
   }
}