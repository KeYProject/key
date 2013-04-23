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

import java.util.List;

import junit.framework.TestCase;

import org.junit.Test;

import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.exception.DSCanceledException;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSProvable;
import de.hentschel.visualdbc.datasource.model.memory.MemoryMethod;
import de.hentschel.visualdbc.datasource.model.memory.MemoryOperationContract;
import de.hentschel.visualdbc.datasource.model.memory.MemoryProof;

/**
 * Tests for {@link AbstractDSProvable}
 * @author Martin Hentschel
 */
public class AbstractDSProvableTest extends TestCase {
   /**
    * Tests {@link AbstractDSProvable#hasInteractiveProof(String)}
    */
   @Test
   public void testHasInteractiveProof() {
      try {
         IDSProvable provable = new MemoryMethod();
         assertFalse(provable.hasInteractiveProof("EnsuresPost"));
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Tests {@link AbstractDSProvable#getInteractiveProof(String)} and
    * also adding and removing proofs
    */
   @Test
   public void testGetProof() {
      try {
         // Create model
         IDSProof a = new MemoryProof();
         IDSProof b = new MemoryProof();
         IDSProof c = new MemoryProof();
         IDSProof d = new MemoryProof();
         PublicAbstractDsProvable provable = new PublicAbstractDsProvable();
         // Add proves
         provable.addProof("a", a);
         provable.addProof("b", b);
         provable.addProof("c", c);
         provable.addProof("d", d);
         assertSame(a, provable.getInteractiveProof("a"));
         assertSame(b, provable.getInteractiveProof("b"));
         assertSame(c, provable.getInteractiveProof("c"));
         assertSame(d, provable.getInteractiveProof("d"));
         assertNull(provable.getInteractiveProof("e"));
         // Remove proof
         provable.removeProof("b");
         assertSame(a, provable.getInteractiveProof("a"));
         assertNull(provable.getInteractiveProof("b"));
         assertSame(c, provable.getInteractiveProof("c"));
         assertSame(d, provable.getInteractiveProof("d"));
         assertNull(provable.getInteractiveProof("e"));
         // Replace proof
         provable.addProof("c", b);
         assertSame(a, provable.getInteractiveProof("a"));
         assertNull(provable.getInteractiveProof("b"));
         assertSame(b, provable.getInteractiveProof("c"));
         assertSame(d, provable.getInteractiveProof("d"));
         assertNull(provable.getInteractiveProof("e"));
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }

   /**
    * Implementation of {@link AbstractDSProvable} that is not abstract
    * and where all methods are public.
    * @author Martin Hentschel
    */
   private static class PublicAbstractDsProvable extends AbstractDSProvable {
      /**
       * {@inheritDoc}
       */
      @Override
      public IDSProof removeProof(String obligation) {
         return super.removeProof(obligation);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void addProof(String obligation, IDSProof proof) {
         super.addProof(obligation, proof);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public List<String> getObligations() throws DSException {
         return null;
      }
   }
   
   /**
    * Tests {@link AbstractDSProvable#isValidObligation(String)}
    */
   @Test
   public void testIsValidObligation() {
      try {
         // Crate test model
         MemoryOperationContract container = new MemoryOperationContract();
         container.getObligations().add("A");
         container.getObligations().add("B");
         container.getObligations().add("C");
         container.getObligations().add("D");
         // Test results
         assertFalse(container.isValidObligation(null));
         assertTrue(container.isValidObligation("A"));
         assertTrue(container.isValidObligation("B"));
         assertTrue(container.isValidObligation("C"));
         assertTrue(container.isValidObligation("D"));
         assertFalse(container.isValidObligation("E"));
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Tests {@link AbstractDSProvable#openInteractiveProof(String)}
    */
   @Test
   public void testOpenInteractiveProof() {
      try {
         // Crate test model
         MemoryOperationContract container = new MemoryOperationContract();
         // Test result
         container.openInteractiveProof("A");
         fail();
      }
      catch (DSCanceledException e) {
         fail(e.getMessage());
      }
      catch (DSException e) {
         assertEquals("Interactive proof solving is not supported.", e.getMessage());
      }
   }
}