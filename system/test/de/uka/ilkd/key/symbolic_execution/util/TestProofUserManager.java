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

package de.uka.ilkd.key.symbolic_execution.util;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Tests for {@link ProofUserManager}.
 * @author Martin Hentschel
 */
public class TestProofUserManager extends TestCase {
   /**
    * Tests {@link ProofUserManager#addUser(de.uka.ilkd.key.proof.Proof, Object)},
    * {@link ProofUserManager#removeUserAndDispose(de.uka.ilkd.key.proof.Proof, Object)},
    * {@link ProofUserManager#getProofs()},
    * {@link ProofUserManager#getUsers(Proof)},
    * {@link ProofUserManager#getEnvironment(Proof)} and
    * {@link ProofUserManager#getProofs(KeYEnvironment)}.
    */
   public void testUserManagement_Environment() {
      Proof firstProof = new Proof(new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Proof secondProof = new Proof(new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Proof thirdProof = new Proof(new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Object firstUser = new Object();
      Object secondUser = new Object();
      Object thirdUser = new Object();
      CustomUserInterface ui = new CustomUserInterface(false);
      KeYEnvironment<?> firstEnv = new KeYEnvironment<CustomUserInterface>(ui, null);
      KeYEnvironment<?> secondEnv = new KeYEnvironment<CustomUserInterface>(ui, null);
      // Add firstProof with firstEnv
      ProofUserManager.getInstance().addUser(firstProof, firstEnv, firstUser);
      assertProofsAndEnvironments(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, new Object[] {}, new Object[] {}, firstEnv, false, new Proof[] {firstProof}, secondEnv, false, new Proof[] {});
      // Add secondProof with secondEnv
      ProofUserManager.getInstance().addUser(secondProof, secondEnv, secondUser);
      assertProofsAndEnvironments(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, new Object[] {secondUser}, new Object[] {}, firstEnv, false, new Proof[] {firstProof}, secondEnv, false, new Proof[] {secondProof});
      // Add thirdProof with firstEnv
      ProofUserManager.getInstance().addUser(thirdProof, firstEnv, thirdUser);
      assertProofsAndEnvironments(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, new Object[] {secondUser}, new Object[] {thirdUser}, firstEnv, false, new Proof[] {firstProof, thirdProof}, secondEnv, false, new Proof[] {secondProof});
      // Remove firstProof from firstEnv
      ProofUserManager.getInstance().removeUserAndDispose(firstProof, firstUser);
      assertProofsAndEnvironments(firstProof, secondProof, thirdProof, true, false, false, new Object[] {}, new Object[] {secondUser}, new Object[] {thirdUser}, firstEnv, false, new Proof[] {thirdProof}, secondEnv, false, new Proof[] {secondProof});
      // Remove secondProof from secondEnv
      ProofUserManager.getInstance().removeUserAndDispose(secondProof, secondUser);
      assertProofsAndEnvironments(firstProof, secondProof, thirdProof, true, true, false, new Object[] {}, new Object[] {}, new Object[] {thirdUser}, firstEnv, false, new Proof[] {thirdProof}, secondEnv, true, new Proof[] {});
      // Remove thirdProof from firstEnv
      ProofUserManager.getInstance().removeUserAndDispose(thirdProof, thirdUser);
      assertProofsAndEnvironments(firstProof, secondProof, thirdProof, true, true, true, new Object[] {}, new Object[] {}, new Object[] {}, firstEnv, true, new Proof[] {}, secondEnv, true, new Proof[] {});
      
   }

   /**
    * Tests the given {@link Proof}s.
    * @param firstProof The first {@link Proof}.
    * @param secondProof The second {@link Proof}.
    * @param thirdProof The third {@link Proof}.
    * @param expectedFirstDisposed Is first {@link Proof} disposed?
    * @param expectedSecondDisposed Is second {@link Proof} disposed?
    * @param expectedThirdDisposed Is third {@link Proof} disposed?
    * @param expectedFirstProofUsers Expected user of the first {@link Proof}.
    * @param expectedSecondProofUsers Expected user of the second {@link Proof}.
    * @param expectedThirdProofUsers Expected user of the third {@link Proof}.
    * @param firstEnv The first {@link KeYEnvironment}.
    * @param firstEnvDisposed Is first {@link KeYEnvironment} disposed?
    * @param firstEnvProofs The expected {@link Proof}s of the first {@link KeYEnvironment}.
    * @param secondEnv The second {@link KeYEnvironment}.
    * @param secondEnvDisposed Is second {@link KeYEnvironment} disposed?
    * @param secondEnvProofs The expected {@link Proof}s of the second {@link KeYEnvironment}.
    */
   private void assertProofsAndEnvironments(Proof firstProof, 
                                            Proof secondProof, 
                                            Proof thirdProof, 
                                            boolean expectedFirstDisposed, 
                                            boolean expectedSecondDisposed, 
                                            boolean expectedThirdDisposed, 
                                            Object[] expectedFirstProofUsers, 
                                            Object[] expectedSecondProofUsers, 
                                            Object[] expectedThirdProofUsers,
                                            KeYEnvironment<?> firstEnv,
                                            boolean firstEnvDisposed,
                                            Proof[] firstEnvProofs, 
                                            KeYEnvironment<?> secondEnv,
                                            boolean secondEnvDisposed,
                                            Proof[] secondEnvProofs) {
      assertNotNull(firstEnv);
      assertNotNull(firstEnvProofs);
      assertNotNull(secondEnv);
      assertNotNull(secondEnvProofs);
      assertProofs(firstProof, secondProof, thirdProof, expectedFirstDisposed, expectedSecondDisposed, expectedThirdDisposed, expectedFirstProofUsers, expectedSecondProofUsers, expectedThirdProofUsers);
      assertEquals(firstEnvDisposed, firstEnv.isDisposed());
      assertEquals(secondEnvDisposed, secondEnv.isDisposed());
      Proof[] proofs = {firstProof, secondProof, thirdProof};
      // Made sure that correct proofs are registered for environments
      for (Proof proof : proofs) {
         if (JavaUtil.contains(firstEnvProofs, proof)) {
            assertEquals(firstEnv, ProofUserManager.getInstance().getEnvironment(proof));
         }
         else if (JavaUtil.contains(secondEnvProofs, proof)) {
            assertEquals(secondEnv, ProofUserManager.getInstance().getEnvironment(proof));
         }
         else {
            assertNull(ProofUserManager.getInstance().getEnvironment(proof));
         }
      }
      // Made sure that correct proofs are known 
      Proof[] currentFirstEnvProofs = ProofUserManager.getInstance().getProofs(firstEnv);
      for (Proof proof : currentFirstEnvProofs) {
         assertTrue(JavaUtil.contains(firstEnvProofs, proof));
      }
      for (Proof proof : firstEnvProofs) {
         assertTrue(JavaUtil.contains(currentFirstEnvProofs, proof));
      }
      Proof[] currentSecondEnvProofs = ProofUserManager.getInstance().getProofs(secondEnv);
      for (Proof proof : currentSecondEnvProofs) {
         assertTrue(JavaUtil.contains(secondEnvProofs, proof));
      }
      for (Proof proof : secondEnvProofs) {
         assertTrue(JavaUtil.contains(currentSecondEnvProofs, proof));
      }
   }

   /**
    * Tests {@link ProofUserManager#addUser(de.uka.ilkd.key.proof.Proof, Object)},
    * {@link ProofUserManager#removeUserAndDispose(de.uka.ilkd.key.proof.Proof, Object)},
    * {@link ProofUserManager#getProofs()} and
    * {@link ProofUserManager#getUsers(Proof)}.
    */
   public void testUserManagement_NoEnvironment() throws Exception {
      Proof firstProof = new Proof(new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Proof secondProof = new Proof(new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Proof thirdProof = new Proof(new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Object firstUser = new Object();
      Object secondUser = new Object();
      Object thirdUser = new Object();
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, null, null, null);
      // Test null parameter
      try {
         ProofUserManager.getInstance().addUser(null, null, firstUser);
         fail();
      }
      catch (Exception e) {
         assertEquals("Proof not defined.", e.getMessage());
      }
      try {
         ProofUserManager.getInstance().removeUserAndDispose(null, firstUser);
         fail();
      }
      catch (Exception e) {
         assertEquals("Proof not defined.", e.getMessage());
      }
      try {
         ProofUserManager.getInstance().addUser(firstProof, null, null);
         fail();
      }
      catch (Exception e) {
         assertEquals("User not defined.", e.getMessage());
      }
      try {
         ProofUserManager.getInstance().removeUserAndDispose(firstProof, null);
         fail();
      }
      catch (Exception e) {
         assertEquals("User not defined.", e.getMessage());
      }
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, null, null, null);
      Object[] nullUser = ProofUserManager.getInstance().getUsers(null);
      assertNotNull(nullUser);
      assertEquals(0, nullUser.length);
      // Test one proof with two users (also remove of not registered users, double adding of users and readding of user)
      ProofUserManager.getInstance().addUser(firstProof, null, firstUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, null, null);
      ProofUserManager.getInstance().addUser(firstProof, null, firstUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, null, null);
      ProofUserManager.getInstance().addUser(firstProof, null, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser, secondUser}, null, null);
      ProofUserManager.getInstance().removeUserAndDispose(firstProof, thirdUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser, secondUser}, null, null);
      ProofUserManager.getInstance().removeUserAndDispose(firstProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, null, null);
      ProofUserManager.getInstance().removeUserAndDispose(firstProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, null, null);
      ProofUserManager.getInstance().addUser(firstProof, null, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser, secondUser}, null, null);
      ProofUserManager.getInstance().removeUserAndDispose(firstProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, null, null);
      ProofUserManager.getInstance().removeUserAndDispose(firstProof, firstUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, null, null);
      // Test two proofs at the same time
      ProofUserManager.getInstance().addUser(secondProof, null, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {secondUser}, null);
      ProofUserManager.getInstance().addUser(thirdProof, null, thirdUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {secondUser}, new Object[] {thirdUser});
      ProofUserManager.getInstance().addUser(thirdProof, null, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {secondUser}, new Object[] {thirdUser, secondUser});
      ProofUserManager.getInstance().removeUserAndDispose(thirdProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {secondUser}, new Object[] {thirdUser});
      ProofUserManager.getInstance().addUser(secondProof, null, firstUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {secondUser, firstUser}, new Object[] {thirdUser});
      ProofUserManager.getInstance().addUser(thirdProof, null, firstUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {secondUser, firstUser}, new Object[] {thirdUser, firstUser});
      ProofUserManager.getInstance().removeUserAndDispose(secondProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {firstUser}, new Object[] {thirdUser, firstUser});
      ProofUserManager.getInstance().removeUserAndDispose(thirdProof, thirdUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {firstUser}, new Object[] {firstUser});
      ProofUserManager.getInstance().removeUserAndDispose(secondProof, firstUser);
      assertProofs(firstProof, secondProof, thirdProof, true, true, false, null, null, new Object[] {firstUser});
      ProofUserManager.getInstance().removeUserAndDispose(thirdProof, firstUser);
      assertProofs(firstProof, secondProof, thirdProof, true, true, true, null, null, null);
      // Test dispose of not registered proof
      Proof fourthProof = new Proof(new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      assertFalse(fourthProof.isDisposed());
      assertEquals(0, ProofUserManager.getInstance().getProofs().length);
      ProofUserManager.getInstance().removeUserAndDispose(fourthProof, new Object());
      assertTrue(fourthProof.isDisposed());
      assertEquals(0, ProofUserManager.getInstance().getProofs().length);
      // Test garbage collection
      Proof fifthProof = new Proof(new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      ProofUserManager.getInstance().addUser(fifthProof, null, new Object());
      assertProofs(fifthProof);
      fifthProof.dispose();
      fifthProof = null;
      Thread.sleep(1000);
      Runtime.getRuntime().gc();
      Thread.sleep(1000);
      assertProofs();
   }
   
   /**
    * Tests the given {@link Proof}s.
    * @param firstProof The first {@link Proof}.
    * @param secondProof The second {@link Proof}.
    * @param thirdProof The third {@link Proof}.
    * @param expectedFirstDisposed Is first {@link Proof} disposed?
    * @param expectedSecondDisposed Is second {@link Proof} disposed?
    * @param expectedThirdDisposed Is third {@link Proof} disposed?
    * @param expectedFirstProofUsers Expected user of the first {@link Proof}.
    * @param expectedSecondProofUsers Expected user of the second {@link Proof}.
    * @param expectedThirdProofUsers Expected user of the third {@link Proof}.
    */
   protected void assertProofs(Proof firstProof, 
                               Proof secondProof, 
                               Proof thirdProof, 
                               boolean expectedFirstDisposed, 
                               boolean expectedSecondDisposed, 
                               boolean expectedThirdDisposed, 
                               Object[] expectedFirstProofUsers, 
                               Object[] expectedSecondProofUsers, 
                               Object[] expectedThirdProofUsers) {
      // Test existing proofs
      assertEquals(expectedFirstDisposed, firstProof.isDisposed());
      assertEquals(expectedSecondDisposed, secondProof.isDisposed());
      assertEquals(expectedThirdDisposed, thirdProof.isDisposed());
      // Test registered proofs
      Proof[] registeredProofs = ProofUserManager.getInstance().getProofs();
      assertNotNull(registeredProofs);
      int expectedCount = 0;
      if (!JavaUtil.isEmpty(expectedFirstProofUsers)) {
         expectedCount++;
         assertTrue(JavaUtil.contains(registeredProofs, firstProof));
         assertUser(firstProof, expectedFirstProofUsers);
      }
      if (!JavaUtil.isEmpty(expectedSecondProofUsers)) {
         expectedCount++;
         assertTrue(JavaUtil.contains(registeredProofs, secondProof));
         assertUser(secondProof, expectedSecondProofUsers);
      }
      if (!JavaUtil.isEmpty(expectedThirdProofUsers)) {
         expectedCount++;
         assertTrue(JavaUtil.contains(registeredProofs, thirdProof));
         assertUser(thirdProof, expectedThirdProofUsers);
      }
      assertEquals(expectedCount, registeredProofs.length);
   }

   /**
    * Makes sure that the given {@link Proof} has the given users.
    * @param proof The {@link Proof} to test its users.
    * @param expectedUsers The expected users.
    */
   private void assertUser(Proof proof, Object... expectedUsers) {
      Object[] users = ProofUserManager.getInstance().getUsers(proof);
      assertNotNull(users);
      assertEquals(expectedUsers.length, users.length);
      for (Object user : expectedUsers) {
         assertTrue(JavaUtil.contains(users, user));
      }
   }

   /**
    * Makes sure that the given {@link Proof}s are registered.
    * @param expectedProofs The expected registered {@link Proof}s.
    */
   private void assertProofs(Proof... expectedProofs) {
      Proof[] proofs = ProofUserManager.getInstance().getProofs();
      assertNotNull(proofs);
      assertEquals(expectedProofs.length, proofs.length);
      for (Proof proof : expectedProofs) {
         assertTrue(JavaUtil.contains(proofs, proof));
      }
   }

   /**
    * Tests {@link ProofUserManager#getInstance()}.
    */
   public void testGetInstance() {
      ProofUserManager first = ProofUserManager.getInstance();
      assertNotNull(first);
      ProofUserManager second = ProofUserManager.getInstance();
      assertSame(first, second);
   }
}