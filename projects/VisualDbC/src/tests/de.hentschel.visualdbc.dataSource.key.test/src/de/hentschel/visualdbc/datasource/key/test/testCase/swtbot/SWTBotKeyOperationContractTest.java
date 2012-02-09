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

package de.hentschel.visualdbc.datasource.key.test.testCase.swtbot;

import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.util.java.CollectionUtil;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil.MethodTreatment;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.model.KeyOperationContract;
import de.hentschel.visualdbc.datasource.key.rule.KeyProofReferenceUtil;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil.IDSProvableReferenceSelector;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil.IDSProvableSelector;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryProvableReference;

/**
 * Tests for {@link KeyOperationContract}
 * @author Martin Hentschel
 */
public class SWTBotKeyOperationContractTest extends TestCase {
   /**
    * Tests {@link IDSProvable#openInteractiveProof(String)} and
    * specially the references of kind "Use Operation Contract".
    */
   @Test
   public void testReferences_useOperationContract() {
      TestKeyUtil.testOpenProof("KeyOperationContract_testReferences_useOperationContract",
                                "data/methodBodyExpandTest",
                                new IDSProvableSelector() {
                                   @Override
                                   public IDSProvable getProvable(IDSConnection con) throws DSException {
                                      IDSClass dsClass = con.getClass("MCDemo");
                                      TestCase.assertNotNull(dsClass);
                                      IDSMethod dsMethod = dsClass.getMethod("init(u : int)");
                                      TestCase.assertNotNull(dsMethod);
                                      IDSOperationContract dsContract = dsMethod.getOperationContracts().get(0);
                                      TestCase.assertNotNull(dsContract);
                                      return dsContract;
                                   }
                                },
                                KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT,
                                "JML normal_behavior operation contract [id: 1 / MCDemo::init]",
                                true,
                                MethodTreatment.CONTRACTS,
                                new IDSProvableReferenceSelector() {
                                   @SuppressWarnings("unchecked")
                                   @Override
                                   public List<List<MemoryProvableReference>> getExpectedProofReferences(IDSConnection con) throws DSException {
                                      List<List<MemoryProvableReference>> result = new LinkedList<List<MemoryProvableReference>>();
                                      IDSClass dsClass = con.getClass("MCDemo");
                                      TestCase.assertNotNull(dsClass);
                                      IDSMethod dsInitMethod = dsClass.getMethod("init(u : int)");
                                      TestCase.assertNotNull(dsInitMethod);
                                      IDSMethod dsIncMethod = dsClass.getMethod("inc(x : int)");
                                      TestCase.assertNotNull(dsIncMethod);
                                      List<MemoryProvableReference> firstEvent = CollectionUtil.toList(new MemoryProvableReference(dsInitMethod, KeyProofReferenceUtil.METHOD_BODY_EXPAND));
                                      result.add(firstEvent);
                                      List<MemoryProvableReference> secondEvent = CollectionUtil.toList(new MemoryProvableReference(dsInitMethod, KeyProofReferenceUtil.METHOD_BODY_EXPAND), new MemoryProvableReference(dsIncMethod.getOperationContracts().get(0), KeyProofReferenceUtil.USE_OPERATION_CONTRACT));
                                      result.add(secondEvent);
                                      return result;
                                   }
                                },
                                false);
   }
   
   /**
    * Tests {@link IDSProvable#openInteractiveProof(String)} and
    * specially the references of kind "Method Body Expand".
    */
   @Test
   public void testReferences_methodBodyExpand() {
      TestKeyUtil.testOpenProof("KeyOperationContract_testReferences_methodBodyExpand",
                                "data/methodBodyExpandTest",
                                new IDSProvableSelector() {
                                   @Override
                                   public IDSProvable getProvable(IDSConnection con) throws DSException {
                                      IDSClass dsClass = con.getClass("MCDemo");
                                      TestCase.assertNotNull(dsClass);
                                      IDSMethod dsMethod = dsClass.getMethod("init(u : int)");
                                      TestCase.assertNotNull(dsMethod);
                                      IDSOperationContract dsContract = dsMethod.getOperationContracts().get(0);
                                      TestCase.assertNotNull(dsContract);
                                      return dsContract;
                                   }
                                },
                                KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT,
                                "JML normal_behavior operation contract [id: 1 / MCDemo::init]",
                                true,
                                MethodTreatment.EXPAND,
                                new IDSProvableReferenceSelector() {
                                   @SuppressWarnings("unchecked")
                                   @Override
                                   public List<List<MemoryProvableReference>> getExpectedProofReferences(IDSConnection con) throws DSException {
                                      List<List<MemoryProvableReference>> result = new LinkedList<List<MemoryProvableReference>>();
                                      IDSClass dsClass = con.getClass("MCDemo");
                                      TestCase.assertNotNull(dsClass);
                                      IDSMethod dsInitMethod = dsClass.getMethod("init(u : int)");
                                      TestCase.assertNotNull(dsInitMethod);
                                      IDSMethod dsIncMethod = dsClass.getMethod("inc(x : int)");
                                      TestCase.assertNotNull(dsIncMethod);
                                      List<MemoryProvableReference> firstEvent = CollectionUtil.toList(new MemoryProvableReference(dsInitMethod, KeyProofReferenceUtil.METHOD_BODY_EXPAND));
                                      result.add(firstEvent);
                                      List<MemoryProvableReference> secondEvent = CollectionUtil.toList(new MemoryProvableReference(dsInitMethod, KeyProofReferenceUtil.METHOD_BODY_EXPAND), new MemoryProvableReference(dsIncMethod, KeyProofReferenceUtil.METHOD_BODY_EXPAND));
                                      result.add(secondEvent);
                                      return result;
                                   }
                                },
                                false);
   }
   
   /**
    * Tests {@link IDSProvable#openInteractiveProof(String)}
    */
   @Test
   public void testOpenInteractiveProof_ContractPO_withInitialReferences() {
      TestKeyUtil.testOpenProof("KeyOperationContract_testOpenInteractiveProof_EnsuresPost_withInitialReferences",
                                "data/quicktour/paycard",
                                new IDSProvableSelector() {
                                   @Override
                                   public IDSProvable getProvable(IDSConnection con) throws DSException {
                                      IDSClass dsClass = con.getClass("paycard.PayCard");
                                      TestCase.assertNotNull(dsClass);
                                      IDSMethod dsMethod = dsClass.getMethod("isValid()");
                                      TestCase.assertNotNull(dsMethod);
                                      IDSOperationContract dsContract = dsMethod.getOperationContracts().get(0);
                                      TestCase.assertNotNull(dsContract);
                                      return dsContract;
                                   }
                                },
                                KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT,
                                "JML normal_behavior operation contract [id: 10 / paycard.PayCard::isValid]",
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
      TestKeyUtil.testOpenProof("KeyOperationContract_testOpenInteractiveProof_EnsuresPost_noInitialReferences",
                                "data/quicktour/paycard",
                                new IDSProvableSelector() {
                                   @Override
                                   public IDSProvable getProvable(IDSConnection con) throws DSException {
                                      IDSClass dsClass = con.getClass("paycard.PayCard");
                                      TestCase.assertNotNull(dsClass);
                                      IDSMethod dsMethod = dsClass.getMethod("isValid()");
                                      TestCase.assertNotNull(dsMethod);
                                      IDSOperationContract dsContract = dsMethod.getOperationContracts().get(0);
                                      TestCase.assertNotNull(dsContract);
                                      return dsContract;
                                   }
                                },
                                KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT,
                                "JML normal_behavior operation contract [id: 10 / paycard.PayCard::isValid]",
                                true,
                                MethodTreatment.EXPAND,
                                null,
                                false);
   }
}
