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

package org.key_project.key4eclipse.util.test.model;

@SuppressWarnings("unused")
public class ClassA {
   private int privateField = 1;
   
   protected int protectedField = 2;
   
   public int publicField = 3;
   
   int defaultField = 4;
   
   private String onlyInA = "A";
   
   private int getPrivate() {
      return 42;
   }
   
   public int getPublic() {
      return 43;
   }
   
   protected int getProtected() {
      return 44;
   }
   
   int getDefault() {
      return 45;
   }
   
   private int getValue(Integer value) {
      return value;
   }
   
   private int getValue(Integer first, Integer second) {
      return first + second;
   }
   
   private String onlyInA() {
      return "A";
   }
}
