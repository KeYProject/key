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

package util;

/**
 * Provides static methods to work with strings.
 * @author Martin Hentschel
 */
public final class StringUtil {
   /**
    * Constant for a line break.
    */
   public static final Object NEW_LINE = System.getProperty("line.separator");
   
   /**
    * Forbid instances by this private constructor.
    */
   private StringUtil() {
   }
}