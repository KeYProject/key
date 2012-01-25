/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.swtbot.swing.finder.matchers;

import java.awt.Component;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import org.eclipse.swt.widgets.Text;
import org.eclipse.swtbot.swt.finder.matchers.AbstractMatcher;
import org.eclipse.swtbot.swt.finder.utils.SWTUtils;
import org.hamcrest.Description;
import org.hamcrest.Factory;
import org.hamcrest.Matcher;

/**
 * <p>
 * Matches {@link Component} if the getTooltip() method of the {@link Component} matches the specified tool tip.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link org.eclipse.swtbot.swt.finder.matchers.WithText}.
 * </p>
 * @author Martin Hentschel
 */
public class WithToolTipText<T> extends AbstractMatcher<T> {
   /**
    * The tool tip
    */
   protected String tooltip;

   /**
    * A flag to denote if this should ignore case.
    */
   protected boolean ignoreCase  = false;
   
   /**
    * Constructs this matcher with the given tool tip.
    * @param tooltip The tool tip to match on the {@link Component}
    */
   WithToolTipText(String tooltip) {
      this(tooltip, false);
   }

   /**
    * Constructs this matcher with the given tool tip.
    * @param tooltip The tool tip to match on the {@link Component}
    * @param ignoreCase Determines if this should ignore case during the comparison.
    */
   WithToolTipText(String tooltip, boolean ignoreCase) {
      tooltip = tooltip.replaceAll("\\r\\n", "\n");
      tooltip = tooltip.replaceAll("\\r", "\n");
      this.tooltip = tooltip;
      this.ignoreCase = ignoreCase;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void describeTo(Description description) {
      description.appendText("with tool tip '").appendText(tooltip).appendText("'");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean doMatch(Object obj) {
      try {
         boolean result = false;
         if (ignoreCase)
            result = getTooltip(obj).equalsIgnoreCase(tooltip);
         else
            result = getTooltip(obj).equals(tooltip);
         return result;
      } catch (Exception e) {
         // do nothing
      }
      return false;
   }
   
   /**
    * Gets the tool tip of the object using the getTooltip method. If the object doesn't contain a get tool tip method an
    * exception is thrown.
    * @param obj any object to get the tool tip from.
    * @return the return value of obj#getTooltip()
    * @throws NoSuchMethodException if the method "getTooltip" does not exist on the object.
    * @throws IllegalAccessException if the java access control does not allow invocation.
    * @throws InvocationTargetException if the method "getTooltip" throws an exception.
    * @see Method#invoke(Object, Object[])
    */   
   static String getTooltip(Object obj) throws NoSuchMethodException, IllegalAccessException, InvocationTargetException {
      return ((String) SWTUtils.invokeMethod(obj, "getToolTipText")).replaceAll(Text.DELIMITER, "\n");
   }
   
   /**
    * Matches a widget that has the specified exact tool tip.
    * @param tooltip the label.
    * @return a matcher.
    */
   @Factory
   public static <T> Matcher<T> withToolTipText(String tooltip) {
      return new WithToolTipText<T>(tooltip);
   }

   /**
    * Matches a widget that has the specified tool tip, ignoring case considerations.
    * @param tooltip the label.
    * @return a matcher.
    */
   @Factory
   public static <T> Matcher<T> withToolTipTextIgnoringCase(String tooltip) {
      return new WithToolTipText<T>(tooltip, true);
   }
}
