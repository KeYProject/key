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

package org.key_project.util.test.model;

@SuppressWarnings("unused")
public class ClassA {
   private int privateField = 1;
   
   protected int protectedField = 2;
   
   public int publicField = 3;
   
   int defaultField = 4;
   
   private String onlyInA = "A";
   
   private boolean booleanField = true;
   
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