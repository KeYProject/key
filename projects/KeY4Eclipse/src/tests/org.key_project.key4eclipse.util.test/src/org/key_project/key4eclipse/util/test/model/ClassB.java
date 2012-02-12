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
