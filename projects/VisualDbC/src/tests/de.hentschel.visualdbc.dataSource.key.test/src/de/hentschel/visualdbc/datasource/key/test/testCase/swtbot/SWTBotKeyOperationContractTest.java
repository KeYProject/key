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

import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.test.util.TestKeY4EclipseUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil.MethodTreatment;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.model.KeyOperationContract;
import de.hentschel.visualdbc.datasource.key.rule.KeyProofReferenceUtil;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil.IDSProvableReferenceSelector;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil.IDSProvableSelector;
import de.hentschel.visualdbc.datasource.model.IDSAttribute;
import de.hentschel.visualdbc.datasource.model.IDSAxiom;
import de.hentschel.visualdbc.datasource.model.IDSAxiomContract;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSEnumLiteral;
import de.hentschel.visualdbc.datasource.model.IDSInvariant;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryProvableReference;

/**
 * Tests for {@link KeyOperationContract}
 * @author Martin Hentschel
 */
public class SWTBotKeyOperationContractTest extends AbstractSetupTestCase {
   /**
    * Tests {@link IDSProvable#openInteractiveProof(String)} and
    * specially the references of kind "Use Invariant".
    */
   @Test
   public void testReferences_useInvariant() {
      TestKeyUtil.testOpenProof("KeyOperationContract_testReferences_useInvariant",
                                "data/accessibleTest",
                                new IDSProvableSelector() {
                                   @Override
                                   public IDSProvable getProvable(IDSConnection con) throws DSException {
                                      IDSClass dsClass = con.getClass("test.B");
                                      TestCase.assertNotNull(dsClass);
                                      IDSAxiom dsAxiom = dsClass.getAxioms().get(0);
                                      TestCase.assertNotNull(dsAxiom);
                                      IDSAxiomContract dsContract = dsAxiom.getAxiomContracts().get(0);
                                      TestCase.assertNotNull(dsContract);
                                      return dsContract;
                                   }
                                },
                                KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT,
                                TestKeY4EclipseUtil.createCompleteAxiomContractId("test.B", "java.lang.Object::<inv>()", "0"),
                                false,
                                MethodTreatment.CONTRACTS,
                                new IDSProvableReferenceSelector() {
                                   @SuppressWarnings("unchecked")
                                   @Override
                                   public List<List<MemoryProvableReference>> getExpectedProofReferences(IDSConnection con) throws DSException {
                                      List<List<MemoryProvableReference>> result = new LinkedList<List<MemoryProvableReference>>();
                                      IDSClass dsClass = con.getClass("test.B");
                                      TestCase.assertNotNull(dsClass);
                                      IDSInvariant dsInvariant = dsClass.getInvariants().get(0);
                                      TestCase.assertNotNull(dsInvariant);
                                      List<MemoryProvableReference> event = CollectionUtil.toList(new MemoryProvableReference(dsInvariant, KeyProofReferenceUtil.USE_INVARIANT));
                                      result.add(event);
                                      return result;
                                   }
                                },
                                false);
   }
   
   /**
    * Tests {@link IDSProvable#openInteractiveProof(String)} and
    * specially the references of kind "Use Axiom".
    */
   @Test
   public void testReferences_useAxiom() {
      TestKeyUtil.testOpenProof("KeyOperationContract_testReferences_useAxiom",
                                "data/modelFieldTest",
                                new IDSProvableSelector() {
                                   @Override
                                   public IDSProvable getProvable(IDSConnection con) throws DSException {
                                      IDSClass dsClass = con.getClass("ModelFieldTest");
                                      TestCase.assertNotNull(dsClass);
                                      IDSAxiom dsAxiom = dsClass.getAxioms().get(0);
                                      TestCase.assertNotNull(dsAxiom);
                                      IDSAxiomContract dsContract = dsAxiom.getAxiomContracts().get(0);
                                      TestCase.assertNotNull(dsContract);
                                      return dsContract;
                                   }
                                },
                                KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT,
                                TestKeY4EclipseUtil.createAxiomContractId("ModelFieldTest", "$f()", "0"),
                                true,
                                MethodTreatment.CONTRACTS,
                                new IDSProvableReferenceSelector() {
                                   @SuppressWarnings("unchecked")
                                   @Override
                                   public List<List<MemoryProvableReference>> getExpectedProofReferences(IDSConnection con) throws DSException {
                                      List<List<MemoryProvableReference>> result = new LinkedList<List<MemoryProvableReference>>();
                                      IDSClass dsClass = con.getClass("ModelFieldTest");
                                      TestCase.assertNotNull(dsClass);
                                      IDSAxiom dsAxiom = dsClass.getAxioms().get(0);
                                      TestCase.assertNotNull(dsAxiom);
                                      List<MemoryProvableReference> event = CollectionUtil.toList(new MemoryProvableReference(dsAxiom, KeyProofReferenceUtil.USE_AXIOM));
                                      result.add(event);
                                      return result;
                                   }
                                },
                                false);
   }
   
   /**
    * Tests {@link IDSProvable#openInteractiveProof(String)} and
    * specially the references of kind "Access".
    */
   @Test
   public void testReferences_readAndWriteAccess() {
      TestKeyUtil.testOpenProof("KeyOperationContract_testReferences_readAndWriteAccess",
                                "data/attributeAndEnumLiteralTest",
                                new IDSProvableSelector() {
                                   @Override
                                   public IDSProvable getProvable(IDSConnection con) throws DSException {
                                      IDSClass dsClass = con.getClass("Main");
                                      TestCase.assertNotNull(dsClass);
                                      IDSMethod dsMethod = dsClass.getMethod("main()");
                                      TestCase.assertNotNull(dsMethod);
                                      IDSOperationContract dsContract = dsMethod.getOperationContracts().get(0);
                                      TestCase.assertNotNull(dsContract);
                                      return dsContract;
                                   }
                                },
                                KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT,
                                TestKeY4EclipseUtil.createOperationContractId("Main", "Main", "main()", "0", "normal_behavior"),
                                true,
                                MethodTreatment.EXPAND,
                                new IDSProvableReferenceSelector() {
                                   @SuppressWarnings("unchecked")
                                   @Override
                                   public List<List<MemoryProvableReference>> getExpectedProofReferences(IDSConnection con) throws DSException {
                                      List<List<MemoryProvableReference>> result = new LinkedList<List<MemoryProvableReference>>();
                                      IDSClass mainClass = con.getClass("Main");
                                      TestCase.assertNotNull(mainClass);
                                      IDSMethod dsMethod = mainClass.getMethod("main()");
                                      TestCase.assertNotNull(dsMethod);
                                      IDSAttribute mainIntValue = mainClass.getAttribute("intValue");
                                      TestCase.assertNotNull(mainIntValue);
                                      IDSAttribute mainObjValue = mainClass.getAttribute("objValue");
                                      TestCase.assertNotNull(mainObjValue);

                                      IDSClass myClass = con.getClass("MyClass");
                                      TestCase.assertNotNull(myClass);
                                      IDSAttribute myClassIntValue = myClass.getAttribute("intValue");
                                      TestCase.assertNotNull(myClassIntValue);
                                      IDSAttribute myClassEnumValue = myClass.getAttribute("enumValue");
                                      TestCase.assertNotNull(myClassEnumValue);
                                      
                                      IDSEnum myEnum = con.getEnum("MyEnum");
                                      TestCase.assertNotNull(myEnum);
                                      IDSAttribute myEnumIntValue = myEnum.getAttribute("intValue");
                                      TestCase.assertNotNull(myEnumIntValue);
                                      IDSEnumLiteral literalA = myEnum.getLiteral("LITERAL_A");
                                      TestCase.assertNotNull(literalA);
                                      
                                      List<MemoryProvableReference> event = CollectionUtil.toList(new MemoryProvableReference(dsMethod, KeyProofReferenceUtil.INLINE_METHOD), 
                                                                                                  new MemoryProvableReference(mainIntValue, KeyProofReferenceUtil.ACCESS), 
                                                                                                  new MemoryProvableReference(mainObjValue, KeyProofReferenceUtil.ACCESS), 
                                                                                                  new MemoryProvableReference(myClassEnumValue, KeyProofReferenceUtil.ACCESS), 
                                                                                                  new MemoryProvableReference(myEnumIntValue, KeyProofReferenceUtil.ACCESS), 
                                                                                                  new MemoryProvableReference(myClassIntValue, KeyProofReferenceUtil.ACCESS), 
                                                                                                  new MemoryProvableReference(literalA, KeyProofReferenceUtil.ACCESS));
                                      result.add(event);
                                      return result;
                                   }
                                },
                                false);
   }
   
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
                                TestKeY4EclipseUtil.createOperationContractId("MCDemo", "MCDemo", "init(int)", "0", "normal_behavior"),
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
                                      IDSAttribute dsAttr = dsClass.getAttribute("attr");
                                      TestCase.assertNotNull(dsAttr);
                                      List<MemoryProvableReference> event = CollectionUtil.toList(new MemoryProvableReference(dsInitMethod, KeyProofReferenceUtil.INLINE_METHOD), 
                                                                                                  new MemoryProvableReference(dsAttr, KeyProofReferenceUtil.ACCESS), 
                                                                                                  new MemoryProvableReference(dsIncMethod.getOperationContracts().get(0), KeyProofReferenceUtil.USE_CONTRACT));
                                      result.add(event);
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
                                TestKeY4EclipseUtil.createOperationContractId("MCDemo", "MCDemo", "init(int)", "0", "normal_behavior"),
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
                                      IDSAttribute dsAttr = dsClass.getAttribute("attr");
                                      TestCase.assertNotNull(dsAttr);
                                      List<MemoryProvableReference> event = CollectionUtil.toList(new MemoryProvableReference(dsInitMethod, KeyProofReferenceUtil.INLINE_METHOD), 
                                                                                                  new MemoryProvableReference(dsAttr, KeyProofReferenceUtil.ACCESS), 
                                                                                                  new MemoryProvableReference(dsIncMethod, KeyProofReferenceUtil.CALL_METHOD),
                                                                                                  new MemoryProvableReference(dsIncMethod, KeyProofReferenceUtil.INLINE_METHOD));
                                      result.add(event);
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
                                "data/quicktour/test/paycard",
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
                                TestKeY4EclipseUtil.createOperationContractId("paycard.PayCard", "paycard.PayCard", "isValid()", "0", "normal_behavior"),
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
                                "data/quicktour/test/paycard",
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
                                TestKeY4EclipseUtil.createOperationContractId("paycard.PayCard", "paycard.PayCard", "isValid()", "0", "normal_behavior"),
                                true,
                                MethodTreatment.EXPAND,
                                null,
                                false);
   }
}