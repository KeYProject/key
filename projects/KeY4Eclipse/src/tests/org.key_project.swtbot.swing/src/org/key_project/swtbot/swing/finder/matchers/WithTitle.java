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
import java.lang.reflect.Method;

import org.eclipse.swt.widgets.Text;
import org.eclipse.swtbot.swt.finder.matchers.AbstractMatcher;
import org.eclipse.swtbot.swt.finder.matchers.WithText;
import org.eclipse.swtbot.swt.finder.utils.SWTUtils;
import org.hamcrest.Description;
import org.hamcrest.Factory;
import org.hamcrest.Matcher;
import org.key_project.swtbot.swing.util.AbstractRunnableWithResultAndException;
import org.key_project.swtbot.swing.util.IRunnableWithResultAndException;
import org.key_project.swtbot.swing.util.SaveSwingUtil;

/**
 * <p>
 * Matches {@link Component} if the getTitle() method of the {@link Component} matches the specified text.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link WithText}.
 * </p>
 * @author Martin Hentschel
 */
public class WithTitle<T> extends AbstractMatcher<T> {
   /**
    * The title
    */
   protected String title;

   /**
    * A flag to denote if this should ignore case.
    */
   protected boolean ignoreCase  = false;
   
   /**
    * Constructs this matcher with the given title.
    * @param title The title to match on the {@link Component}
    */
   WithTitle(String title) {
      this(title, false);
   }

   /**
    * Constructs this matcher with the given title.
    * @param title The title to match on the {@link Component}
    * @param ignoreCase Determines if this should ignore case during the comparison.
    */
   WithTitle(String title, boolean ignoreCase) {
      title = title.replaceAll("\\r\\n", "\n");
      title = title.replaceAll("\\r", "\n");
      this.title = title;
      this.ignoreCase = ignoreCase;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void describeTo(Description description) {
      description.appendText("with title '").appendText(title).appendText("'");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean doMatch(Object obj) {
      try {
         boolean result = false;
         if (ignoreCase)
            result = getTitle(obj).equalsIgnoreCase(title);
         else
            result = getTitle(obj).equals(title);
         return result;
      } catch (Exception e) {
         // do nothing
      }
      return false;
   }
   
   /**
    * Gets the title of the object using the getTitle method. If the object doesn't contain a get title method an
    * exception is thrown.
    * @param obj any object to get the title from.
    * @return the return value of obj#getTitle()
    * @see Method#invoke(Object, Object[])
    */   
   static String getTitle(final Object obj) throws Exception {
      IRunnableWithResultAndException<String> run = new AbstractRunnableWithResultAndException<String>() {
         @Override
         public void run() {
            try {
               setResult(((String) SWTUtils.invokeMethod(obj, "getTitle")).replaceAll(Text.DELIMITER, "\n"));
            }
            catch (Exception e) {
               setException(e);
            }
         }
      };
      SaveSwingUtil.invokeAndWait(run);
      if (run.getException() != null) {
         throw run.getException();
      }
      return run.getResult();
   }
   
   /**
    * Matches a widget that has the specified exact title.
    * @param title the label.
    * @return a matcher.
    */
   @Factory
   public static <T> Matcher<T> withTitle(String title) {
      return new WithTitle<T>(title);
   }

   /**
    * Matches a widget that has the specified title, ignoring case considerations.
    * @param title the label.
    * @return a matcher.
    */
   @Factory
   public static <T> Matcher<T> withTitleIgnoringCase(String title) {
      return new WithTitle<T>(title, true);
   }
}