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
import java.util.Arrays;

import org.eclipse.swtbot.swt.finder.matchers.AbstractMatcher;
import org.hamcrest.Description;
import org.hamcrest.Factory;
import org.hamcrest.Matcher;

/**
 * <p>
 * A matcher that evaluates to {@code true} if and only if all the matchers evaluate to {@code true}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.matchers.AllOf}.
 * </p>
 * @author Martin Hentschel
 */
public class AllOf<T> extends AbstractMatcher<T> {
   /**
    * The {@link Matcher} to use as children.
    */
   private final Iterable<Matcher<? extends T>> matchers;

   /**
    * Constructor.
    * @param matchers The {@link Matcher} to use as children.
    */
   AllOf(Iterable<Matcher<? extends T>> matchers) {
      this.matchers = matchers;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean doMatch(Object o) {
      for (Matcher<? extends T> matcher : matchers) {
         if (!matcher.matches(o)) {
            return false;
         }
      }
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void describeTo(Description description) {
      description.appendList("(", " and ", ")", matchers);
   }

   /**
    * Evaluates to true only if ALL of the passed in matchers evaluate to true.
    * @param <T> The expected {@link Component} type.
    * @param matchers The {@link Matcher} to use as children.
    * @return a matcher.
    */
   @Factory
   public static <T extends Component> Matcher<T> allOf(Matcher<? extends T>... matchers) {
      return new AllOf<T>(Arrays.asList(matchers));
   }
   
   /**
    * Evaluates to true only if ALL of the passed in matchers evaluate to true.
    * @param <T> The expected {@link Component} type.
    * @param matchers The {@link Matcher} to use as children.
    * @return a matcher.
    */
   @Factory
   public static <T extends Component> Matcher<T> allOf(Iterable<Matcher<? extends T>> matchers) {
      return new AllOf<T>(matchers);
   }
}