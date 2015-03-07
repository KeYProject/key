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

package de.hentschel.visualdbc.datasource.test.testCase;

import junit.framework.TestCase;

import org.junit.Test;

import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSOperation;
import de.hentschel.visualdbc.datasource.model.memory.MemoryOperation;
import de.hentschel.visualdbc.datasource.model.memory.MemoryOperationContract;

/**
 * Tests for {@link AbstractDSOperation}
 * @author Martin Hentschel
 */
public class AbstractDSOperationTest extends TestCase {
   /**
    * Tests {@link AbstractDSOperation#getOperationContract(String, String)}
    */
   @Test
   public void testGetOperationContract() {
      try {
         // Crate test model
         MemoryOperationContract a = new MemoryOperationContract("A", "D", "A", "X", "Y");
         MemoryOperationContract b = new MemoryOperationContract("B", "C", "B", "X", "Y");
         MemoryOperationContract c = new MemoryOperationContract("C", "B", "C", "X", "Y");
         MemoryOperationContract d = new MemoryOperationContract("D", "A", "D", "X", "Y");
         MemoryOperation container = new MemoryOperation();
         container.getOperationContracts().add(a);
         container.getOperationContracts().add(b);
         container.getOperationContracts().add(c);
         container.getOperationContracts().add(d);
         // Test results
         assertNull(container.getOperationContract("D", null));
         assertNull(container.getOperationContract(null, "A"));
         assertNull(container.getOperationContract(null, null));
         assertEquals(a, container.getOperationContract("D", "A"));
         assertEquals(b, container.getOperationContract("C", "B"));
         assertEquals(c, container.getOperationContract("B", "C"));
         assertEquals(d, container.getOperationContract("A", "D"));
         assertNull(container.getOperationContract("D", "E"));
         assertNull(container.getOperationContract("E", "E"));
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
}