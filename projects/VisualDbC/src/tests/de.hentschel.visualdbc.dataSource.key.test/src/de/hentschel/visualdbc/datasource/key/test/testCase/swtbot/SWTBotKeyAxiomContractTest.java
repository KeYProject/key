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

package de.hentschel.visualdbc.datasource.key.test.testCase.swtbot;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.test.util.TestKeY4EclipseUtil;
import org.key_project.util.test.util.TestUtilsUtil.MethodTreatment;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.model.KeyOperationContract;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil.IDSProvableSelector;
import de.hentschel.visualdbc.datasource.model.IDSAxiom;
import de.hentschel.visualdbc.datasource.model.IDSAxiomContract;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Tests for {@link KeyOperationContract}
 * @author Martin Hentschel
 */
public class SWTBotKeyAxiomContractTest extends TestCase {
   /**
    * Tests {@link IDSProvable#openInteractiveProof(String)}
    */
   @Test
   public void testOpenInteractiveProof_ContractPO_withInitialReferences() {
      TestKeyUtil.testOpenProof("SWTBotKeyAxiomContractTest_testOpenInteractiveProof_ContractPO_withInitialReferences",
                                "data/modelFieldTest",
                                new IDSProvableSelector() {
                                   @Override
                                   public IDSProvable getProvable(IDSConnection con) throws DSException {
                                      IDSClass dsClass = con.getClass("ModelFieldTest");
                                      TestCase.assertNotNull(dsClass);
                                      IDSAxiom dsAxiom = dsClass.getAxiom("equals(ModelFieldTest::$f(heap,self),javaMulInt(Z(2(#)),int::select(heap,self,ModelFieldTest::$x)))");
                                      TestCase.assertNotNull(dsAxiom);
                                      IDSAxiomContract dsContract = dsAxiom.getAxiomContracts().get(0);
                                      TestCase.assertNotNull(dsContract);
                                      return dsContract;
                                   }
                                },
                                KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT,
                                TestKeY4EclipseUtil.createAxiomContractId("ModelFieldTest", "$f()", "0"),
                                true,
                                MethodTreatment.EXPAND,
                                null,
                                true);
   }
   
   /**
    * Tests {@link IDSProvable#openInteractiveProof(String)}
    */
   @Test
   public void testOpenInteractiveProof_ContractPO_noInitialReferences() {
      TestKeyUtil.testOpenProof("SWTBotKeyAxiomContractTest_testOpenInteractiveProof_ContractPO_noInitialReferences",
                                "data/modelFieldTest",
                                new IDSProvableSelector() {
                                   @Override
                                   public IDSProvable getProvable(IDSConnection con) throws DSException {
                                      IDSClass dsClass = con.getClass("ModelFieldTest");
                                      TestCase.assertNotNull(dsClass);
                                      IDSAxiom dsAxiom = dsClass.getAxiom("equals(ModelFieldTest::$f(heap,self),javaMulInt(Z(2(#)),int::select(heap,self,ModelFieldTest::$x)))");
                                      TestCase.assertNotNull(dsAxiom);
                                      IDSAxiomContract dsContract = dsAxiom.getAxiomContracts().get(0);
                                      TestCase.assertNotNull(dsContract);
                                      return dsContract;
                                   }
                                },
                                KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT,
                                TestKeY4EclipseUtil.createAxiomContractId("ModelFieldTest", "$f()", "0"),
                                true,
                                MethodTreatment.EXPAND,
                                null,
                                false);
   }
}