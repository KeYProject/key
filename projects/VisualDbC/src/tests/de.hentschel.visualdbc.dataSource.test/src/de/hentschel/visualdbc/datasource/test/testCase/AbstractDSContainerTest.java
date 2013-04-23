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
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSContainer;
import de.hentschel.visualdbc.datasource.model.memory.MemoryClass;
import de.hentschel.visualdbc.datasource.model.memory.MemoryEnum;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInterface;
import de.hentschel.visualdbc.datasource.model.memory.MemoryPackage;

/**
 * Contains tests for {@link AbstractDSContainer}
 * @author Martin Hentschel
 */
public class AbstractDSContainerTest extends TestCase {
   /**
    * Tests for {@link AbstractDSContainer#getEnum(String)}
    */
   @Test
   public void testGetEnum() {
      try {
         // Crate test model
         MemoryEnum a = new MemoryEnum("A");
         MemoryEnum b = new MemoryEnum("B");
         MemoryEnum c = new MemoryEnum("C");
         MemoryEnum d = new MemoryEnum("D");
         MemoryPackage container = new MemoryPackage();
         container.getEnums().add(a);
         container.getEnums().add(b);
         container.getEnums().add(c);
         container.getEnums().add(d);
         // Test results
         assertNull(container.getEnum(null));
         assertEquals(a, container.getEnum("A"));
         assertEquals(b, container.getEnum("B"));
         assertEquals(c, container.getEnum("C"));
         assertEquals(d, container.getEnum("D"));
         assertNull(container.getEnum("E"));
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Tests for {@link AbstractDSContainer#getInterface(String)}
    */
   @Test
   public void testGetInterface() {
      try {
         // Crate test model
         MemoryInterface a = new MemoryInterface("A");
         MemoryInterface b = new MemoryInterface("B");
         MemoryInterface c = new MemoryInterface("C");
         MemoryInterface d = new MemoryInterface("D");
         MemoryPackage container = new MemoryPackage();
         container.getInterfaces().add(a);
         container.getInterfaces().add(b);
         container.getInterfaces().add(c);
         container.getInterfaces().add(d);
         // Test results
         assertNull(container.getInterface(null));
         assertEquals(a, container.getInterface("A"));
         assertEquals(b, container.getInterface("B"));
         assertEquals(c, container.getInterface("C"));
         assertEquals(d, container.getInterface("D"));
         assertNull(container.getInterface("E"));
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Tests for {@link AbstractDSContainer#getClass(String)}
    */
   @Test
   public void testGetClass() {
      try {
         // Crate test model
         MemoryClass a = new MemoryClass("A");
         MemoryClass b = new MemoryClass("B");
         MemoryClass c = new MemoryClass("C");
         MemoryClass d = new MemoryClass("D");
         MemoryPackage container = new MemoryPackage();
         container.getClasses().add(a);
         container.getClasses().add(b);
         container.getClasses().add(c);
         container.getClasses().add(d);
         // Test results
         assertNull(container.getClass(null));
         assertEquals(a, container.getClass("A"));
         assertEquals(b, container.getClass("B"));
         assertEquals(c, container.getClass("C"));
         assertEquals(d, container.getClass("D"));
         assertNull(container.getClass("E"));
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Tests for {@link AbstractDSContainer#getPackage(String)}
    */
   @Test
   public void testGetPackage() {
      try {
         // Crate test model
         MemoryPackage a = new MemoryPackage("A");
         MemoryPackage b = new MemoryPackage("B");
         MemoryPackage c = new MemoryPackage("C");
         MemoryPackage d = new MemoryPackage("D");
         MemoryPackage container = new MemoryPackage();
         container.getPackages().add(a);
         container.getPackages().add(b);
         container.getPackages().add(c);
         container.getPackages().add(d);
         // Test results
         assertNull(container.getPackage(null));
         assertEquals(a, container.getPackage("A"));
         assertEquals(b, container.getPackage("B"));
         assertEquals(c, container.getPackage("C"));
         assertEquals(d, container.getPackage("D"));
         assertNull(container.getPackage("E"));
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
}