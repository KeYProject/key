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

/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package de.hentschel.visualdbc.dbcmodel.tests;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation;
import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Abstract Dbc Operation</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following operations are tested:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getOperationContract(java.lang.String, java.lang.String) <em>Get Operation Contract</em>}</li>
 * </ul>
 * </p>
 * @generated
 */
public abstract class AbstractDbcOperationTest extends AbstractDbcProofContainerTest {

   /**
    * Constructs a new Abstract Dbc Operation test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public AbstractDbcOperationTest(String name) {
      super(name);
   }

   /**
    * Returns the fixture for this Abstract Dbc Operation test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected AbstractDbcOperation getFixture() {
      return (AbstractDbcOperation)fixture;
   }

   /**
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getOperationContract(java.lang.String, java.lang.String) <em>Get Operation Contract</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getOperationContract(java.lang.String, java.lang.String)
    * @generated NOT
    */
   public void testGetOperationContract__String_String() {
      // Create model
      AbstractDbcOperation container = DbcmodelFactory.eINSTANCE.createDbcMethod();
      DbcOperationContract contractA = DbcmodelFactory.eINSTANCE.createDbcOperationContract();
      contractA.setName("contractA");
      contractA.setPre("contractAPre");
      contractA.setPost("contractAPost");
      container.getOperationContracts().add(contractA);
      DbcOperationContract contractB = DbcmodelFactory.eINSTANCE.createDbcOperationContract();
      contractB.setName("contractB");
      contractB.setPre("contractBPre");
      contractB.setPost("contractAPost");
      container.getOperationContracts().add(contractB);
      DbcOperationContract contractC = DbcmodelFactory.eINSTANCE.createDbcOperationContract();
      contractC.setName("contractC");
      contractC.setPre("contractBPre");
      contractC.setPost("contractCPost");
      container.getOperationContracts().add(contractC);
      DbcOperationContract contractD = DbcmodelFactory.eINSTANCE.createDbcOperationContract();
      contractD.setName("contractD");
      contractD.setPre("contractDPre");
      contractD.setPost("contractDPost");
      // Execute test
      assertEquals(contractA, container.getOperationContract(contractA.getPre(), contractA.getPost()));
      assertEquals(contractB, container.getOperationContract(contractB.getPre(), contractB.getPost()));
      assertEquals(contractC, container.getOperationContract(contractC.getPre(), contractC.getPost()));
      assertNull(container.getOperationContract(contractD.getPre(), contractD.getPost()));
   }

} //AbstractDbcOperationTest