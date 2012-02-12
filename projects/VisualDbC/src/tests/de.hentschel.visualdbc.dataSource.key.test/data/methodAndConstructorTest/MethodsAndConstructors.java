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

import java.util.Collection;


public abstract class MethodsAndConstructors extends MethodsAndConstructorsParent {
   public MethodsAndConstructors() {
   }

   public MethodsAndConstructors(MyClass c) {
   }

   private MethodsAndConstructors(int i) {
   }

   protected MethodsAndConstructors(String j) {
   }

   MethodsAndConstructors(int i, String j) {
   }
   
   public void doSomething() {
   }
   
   public int doSomething(int i) {
      return 0;
   }
   
   private String doSomethingElse(int[] i) {
      return null;
   }
   
   private String doSomethingElse(int[][] i) {
      return null;
   }
   
   protected String[] doSomethingArray(String[] sArray, MyClass[] myArray, boolean[] boolArray) {
	   return null;
   }
   
// Not supported by KeY??
//   public <T> T doCollection(T t) {
//	   return null;
//   }
   
// Not correctly supported by KeY??
//   public void doEndlesParameter(String... x) {
//   }
   
   double doSomethingElse(int i, MyClass c) {
      return 0.0;
   }
   
   static double doStatic(int i, MyClass c) {
      return 0.0;
   }
   
   public static final void doStatic(String x) {
   }
   
   protected abstract MyClass doAbstract(String x);
}
