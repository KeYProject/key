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

package packageA;

import interfaces.MyInterface;

public interface InterfaceContainer {
   class DefaultChildClass {
      private int x;
      
      public DefaultChildClass(int x) {
         this.x = x;
      }
      
      public void run() {
         new MyInterface() {
         };
      }
   }
	
   public final class PublicChildClass {
      public class InnerInnerClass {
         public void innerInnerRun() {
            new MyInterface() {
            };
         }
      }
   }
   
   interface DefaultChildInterface {
      public interface InnerInnerInterface {
      }
      
      public class InnerInnerClass {
         public void innerInnerRun() {
            new MyInterface() {
            };
         }
      }
   }
	
   public abstract interface PublicChildInterface {
   }
}
