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

package org.key_project.swtbot.swing.finder.matchers;

import java.awt.Component;

import org.hamcrest.Description;
import org.hamcrest.Factory;
import org.hamcrest.Matcher;

/**
 * <p>
 * Matches {@link Component} if the getText() method of the {@link Component} starts with the specified text.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.matchers.WithText}.
 * </p>
 * @author Martin Hentschel
 */
public class WithStartingText<T> extends WithText<T> {
   /**
    * Constructs this matcher with the given text.
    * @param text The text to match on the {@link Component}
    */
   WithStartingText(String text) {
      super(text);
   }

   /**
    * Constructs this matcher with the given text.
    * @param text The text to match on the {@link Component}
    * @param ignoreCase Determines if this should ignore case during the comparison.
    */
   WithStartingText(String text, boolean ignoreCase) {
      super(text, ignoreCase);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void describeTo(Description description) {
      description.appendText("with starting text '").appendText(text).appendText("'");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean doMatch(Object obj) {
      try {
         boolean result = false;
         if (ignoreCase)
            result = getText(obj).toLowerCase().startsWith(text.toLowerCase());
         else
            result = getText(obj).startsWith(text);
         return result;
      } catch (Exception e) {
         // do nothing
      }
      return false;
   }
   
   /**
    * Matches a widget that starts with the specified text.
    * @param text the label.
    * @return a matcher.
    */
   @Factory
   public static <T> Matcher<T> withStartingText(String text) {
      return new WithStartingText<T>(text);
   }

   /**
    * Matches a widget that starts with the specified text, ignoring case considerations.
    * @param text the label.
    * @return a matcher.
    */
   @Factory
   public static <T> Matcher<T> withStartingTextIgnoringCase(String text) {
      return new WithStartingText<T>(text, true);
   }
}