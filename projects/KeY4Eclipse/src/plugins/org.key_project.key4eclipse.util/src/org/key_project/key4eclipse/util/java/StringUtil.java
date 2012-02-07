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

package org.key_project.key4eclipse.util.java;

/**
 * Provides static methods to work with strings.
 * @author Martin Hentschel
 */
public final class StringUtil {
   /**
    * Constant for an empty string.
    */
   public static final String EMPTY_STRING = "";

   /**
    * Constant for a line break.
    */
   public static final Object NEW_LINE = System.getProperty("line.separator");
   
   /**
    * Forbid instances by this private constructor.
    */
   private StringUtil() {
   }
   
   /**
    * Checks if the {@link String} is empty.
    * @param text The text to check.
    * @return {@code true} = text is {@code null} or empty, {@code false} = text is not empty.
    */
   public static boolean isEmpty(String text) {
      return text == null || text.isEmpty();
   }

   /**
    * Checks if the trimmed {@link String} is empty.
    * @param text The text to check.
    * @return {@code true} = text is {@code null} or trimmed empty, {@code false} = text is not empty.
    */
   public static boolean isTrimmedEmpty(String text) {
      return text == null || text.trim().isEmpty();
   }

   /**
    * Nullpointer save execution of {@link String#trim()}
    * @param text The text.
    * @return The trimmed text.
    */
   public static String trim(String text) {
      return text != null ? text.trim() : null;
   }

   /**
    * Nullpointer save execution of {@link String#toLowerCase()}.
    * @param text The text to convert.
    * @return The text in lower case or {@code null} if the given text is {@code null}.
    */
   public static String toLowerCase(String text) {
       return text != null ? text.toLowerCase() : null;
   }
}
