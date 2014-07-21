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

import org.hamcrest.Description;
import org.hamcrest.Factory;
import org.hamcrest.Matcher;

/**
 * <p>
 * Matches {@link Component} if the getTitle() method of the {@link Component} starts with the specified title.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.matchers.WithText}.
 * </p>
 * @author Martin Hentschel
 */
public class WithStartingTitle<T> extends WithTitle<T> {
   /**
    * Constructs this matcher with the given title.
    * @param title The title to match on the {@link Component}
    */
   WithStartingTitle(String title) {
      super(title);
   }

   /**
    * Constructs this matcher with the given title.
    * @param title The title to match on the {@link Component}
    * @param ignoreCase Determines if this should ignore case during the comparison.
    */
   WithStartingTitle(String title, boolean ignoreCase) {
      super(title, ignoreCase);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void describeTo(Description description) {
      description.appendText("with starting title '").appendText(title).appendText("'");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean doMatch(Object obj) {
      try {
         boolean result = false;
         if (ignoreCase)
            result = getTitle(obj).toLowerCase().startsWith(title.toLowerCase());
         else
            result = getTitle(obj).startsWith(title);
         return result;
      } catch (Exception e) {
         // do nothing
      }
      return false;
   }
   
   /**
    * Matches a widget that starts with the specified title.
    * @param title the label.
    * @return a matcher.
    */
   @Factory
   public static <T> Matcher<T> withStartingTitle(String title) {
      return new WithStartingTitle<T>(title);
   }

   /**
    * Matches a widget that starts with the specified title, ignoring case considerations.
    * @param title the label.
    * @return a matcher.
    */
   @Factory
   public static <T> Matcher<T> withStartingTitleIgnoringCase(String title) {
      return new WithStartingTitle<T>(title, true);
   }
}