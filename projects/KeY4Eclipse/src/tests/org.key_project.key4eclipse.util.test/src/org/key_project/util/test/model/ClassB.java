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
public class ClassB extends ClassA {
   private int privateField = 42;
   
   protected int protectedField = 43;
   
   public int publicField = 44;
   
   int defaultField = 45;
   
   private String onlyInB = "B";
   
   private int getPrivate() {
      return 662;
   }
   
   public int getPublic() {
      return 663;
   }
   
   protected int getProtected() {
      return 664;
   }
   
   int getDefault() {
      return 665;
   }
   
   private String onlyInB() {
      return "B";
   }
}