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

import org.eclipse.swtbot.swt.finder.matchers.AbstractMatcher;
import org.eclipse.swtbot.swt.finder.matchers.WidgetOfType;
import org.hamcrest.Description;
import org.hamcrest.Factory;
import org.hamcrest.Matcher;

/**
 * <p>
 * Tells if a particular {@link Component} is of a specified type.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link WidgetOfType}.
 * </p>
 * @author Martin Hentschel
 */
public class ComponentOfType<T extends Component> extends AbstractMatcher<T> {
   /**
    * The type of {@link Component} to match.
    */
   private Class<? extends Component>  type;

   /**
    * Matches a {@link Component} that has the specified type
    * @param type the type of the {@link Component}.
    */   
   ComponentOfType(Class<? extends Component> type) {
      this.type = type;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean doMatch(Object obj) {
      return type.isInstance(obj);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void describeTo(Description description) {
      description.appendText("of type '").appendText(type.getSimpleName()).appendText("'");
   }

   /**
    * Matches a widget that has the specified type
    * @param <T> The type of the expected {@link Component}s.
    * @param type the type of the widget.
    * @return a matcher.
    */
   @Factory
   public static <T extends Component> Matcher<T> componentOfType(Class<T> type) {
      return new ComponentOfType<T>(type);
   }
}