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

package de.hentschel.visualdbc.datasource.test.testCase;

import junit.framework.TestCase;

import org.junit.Test;

import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSType;
import de.hentschel.visualdbc.datasource.model.memory.MemoryClass;
import de.hentschel.visualdbc.datasource.model.memory.MemoryEnum;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInterface;

/**
 * Contains tests for {@link AbstractDSType}
 * @author Martin Hentschel
 */
public class AbstractDSTypeTest extends TestCase {
   /**
    * Tests for {@link AbstractDSType#getInnerEnum(String)}
    */
   @Test
   public void testGetInnerEnum() {
      try {
         // Crate test model
         MemoryEnum a = new MemoryEnum("A");
         MemoryEnum b = new MemoryEnum("B");
         MemoryEnum c = new MemoryEnum("C");
         MemoryEnum d = new MemoryEnum("D");
         MemoryClass container = new MemoryClass();
         container.getInnerEnums().add(a);
         container.getInnerEnums().add(b);
         container.getInnerEnums().add(c);
         container.getInnerEnums().add(d);
         // Test results
         assertNull(container.getInnerEnum(null));
         assertEquals(a, container.getInnerEnum("A"));
         assertEquals(b, container.getInnerEnum("B"));
         assertEquals(c, container.getInnerEnum("C"));
         assertEquals(d, container.getInnerEnum("D"));
         assertNull(container.getInnerEnum("E"));
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Tests for {@link AbstractDSType#getInnerInterface(String)}
    */
   @Test
   public void testGetInnerInterface() {
      try {
         // Crate test model
         MemoryInterface a = new MemoryInterface("A");
         MemoryInterface b = new MemoryInterface("B");
         MemoryInterface c = new MemoryInterface("C");
         MemoryInterface d = new MemoryInterface("D");
         MemoryEnum container = new MemoryEnum();
         container.getInnerInterfaces().add(a);
         container.getInnerInterfaces().add(b);
         container.getInnerInterfaces().add(c);
         container.getInnerInterfaces().add(d);
         // Test results
         assertNull(container.getInnerInterface(null));
         assertEquals(a, container.getInnerInterface("A"));
         assertEquals(b, container.getInnerInterface("B"));
         assertEquals(c, container.getInnerInterface("C"));
         assertEquals(d, container.getInnerInterface("D"));
         assertNull(container.getInnerInterface("E"));
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Tests for {@link AbstractDSType#getInnerClass(String)}
    */
   @Test
   public void testGetInnerClass() {
      try {
         // Crate test model
         MemoryClass a = new MemoryClass("A");
         MemoryClass b = new MemoryClass("B");
         MemoryClass c = new MemoryClass("C");
         MemoryClass d = new MemoryClass("D");
         MemoryInterface container = new MemoryInterface();
         container.getInnerClasses().add(a);
         container.getInnerClasses().add(b);
         container.getInnerClasses().add(c);
         container.getInnerClasses().add(d);
         // Test results
         assertNull(container.getInnerClass(null));
         assertEquals(a, container.getInnerClass("A"));
         assertEquals(b, container.getInnerClass("B"));
         assertEquals(c, container.getInnerClass("C"));
         assertEquals(d, container.getInnerClass("D"));
         assertNull(container.getInnerClass("E"));
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
}