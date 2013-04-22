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

import org.eclipse.swtbot.swt.finder.matchers.AbstractMatcher;
import org.eclipse.swtbot.swt.finder.matchers.WidgetOfType;
import org.hamcrest.Description;
import org.hamcrest.Factory;
import org.hamcrest.Matcher;

/**
 * <p>
 * Tells if a particular {@link Component} is visible or not.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link WidgetOfType}.
 * </p>
 * @author Martin Hentschel
 */
public class ComponentVisibility<T extends Component> extends AbstractMatcher<T> {
   /**
    * The expected visibility.
    */
   private boolean expectedVisibility;

   /**
    * Matches a {@link Component} that has the specified type
    * @param expectedVisibility The expected visibility.
    */   
   ComponentVisibility(boolean expectedVisibility) {
      this.expectedVisibility = expectedVisibility;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean doMatch(Object obj) {
      return obj instanceof Component && ((Component)obj).isVisible() == expectedVisibility;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void describeTo(Description description) {
      description.appendText("is visible '").appendText(expectedVisibility + "").appendText("'");
   }

   /**
    * Matches a widget that is visible.
    * @param <T> The type of the expected {@link Component}s.
    * @param expectedVisibility The expected visibility.
    * @return a matcher.
    */
   @Factory
   public static <T extends Component> Matcher<T> componentVisibility(boolean expectedVisibility) {
      return new ComponentVisibility<T>(expectedVisibility);
   }
}