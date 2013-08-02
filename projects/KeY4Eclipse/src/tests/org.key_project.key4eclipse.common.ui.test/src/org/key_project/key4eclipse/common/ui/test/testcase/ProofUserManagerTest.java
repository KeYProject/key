package org.key_project.key4eclipse.common.ui.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.common.ui.util.ProofUserManager;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;

/**
 * Tests for {@link ProofUserManager}.
 * @author Martin Hentschel
 */
public class ProofUserManagerTest extends TestCase {
   /**
    * Tests {@link ProofUserManager#addUser(de.uka.ilkd.key.proof.Proof, Object)},
    * {@link ProofUserManager#removeUserAndDispose(de.uka.ilkd.key.proof.Proof, Object)},
    * {@link ProofUserManager#getProofs()} and
    * {@link ProofUserManager#getUsers(Proof)}.
    */
   @Test
   public void testUserManagement() {
      Proof firstProof = new Proof(new Services(AbstractProfile.getDefaultProfile()));
      Proof secondProof = new Proof(new Services(AbstractProfile.getDefaultProfile()));
      Proof thirdProof = new Proof(new Services(AbstractProfile.getDefaultProfile()));
      Object firstUser = new Object();
      Object secondUser = new Object();
      Object thirdUser = new Object();
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, null, null, null);
      // Test null parameter
      try {
         ProofUserManager.getInstance().addUser(null, firstUser);
         fail();
      }
      catch (Exception e) {
         assertEquals("null argument:Proof not defined.", e.getMessage());
      }
      try {
         ProofUserManager.getInstance().removeUserAndDispose(null, firstUser);
         fail();
      }
      catch (Exception e) {
         assertEquals("null argument:Proof not defined.", e.getMessage());
      }
      try {
         ProofUserManager.getInstance().addUser(firstProof, null);
         fail();
      }
      catch (Exception e) {
         assertEquals("null argument:User not defined.", e.getMessage());
      }
      try {
         ProofUserManager.getInstance().removeUserAndDispose(firstProof, null);
         fail();
      }
      catch (Exception e) {
         assertEquals("null argument:User not defined.", e.getMessage());
      }
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, null, null, null);
      Object[] nullUser = ProofUserManager.getInstance().getUsers(null);
      assertNotNull(nullUser);
      assertEquals(0, nullUser.length);
      // Test one proof with two users (also remove of not registered users, double adding of users and readding of user)
      ProofUserManager.getInstance().addUser(firstProof, firstUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, null, null);
      ProofUserManager.getInstance().addUser(firstProof, firstUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, null, null);
      ProofUserManager.getInstance().addUser(firstProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser, secondUser}, null, null);
      ProofUserManager.getInstance().removeUserAndDispose(firstProof, thirdUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser, secondUser}, null, null);
      ProofUserManager.getInstance().removeUserAndDispose(firstProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, null, null);
      ProofUserManager.getInstance().removeUserAndDispose(firstProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, null, null);
      ProofUserManager.getInstance().addUser(firstProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser, secondUser}, null, null);
      ProofUserManager.getInstance().removeUserAndDispose(firstProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, false, false, false, new Object[] {firstUser}, null, null);
      ProofUserManager.getInstance().removeUserAndDispose(firstProof, firstUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, null, null);
      // Test two proofs at the same time
      ProofUserManager.getInstance().addUser(secondProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {secondUser}, null);
      ProofUserManager.getInstance().addUser(thirdProof, thirdUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {secondUser}, new Object[] {thirdUser});
      ProofUserManager.getInstance().addUser(thirdProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {secondUser}, new Object[] {thirdUser, secondUser});
      ProofUserManager.getInstance().removeUserAndDispose(thirdProof, secondUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {secondUser}, new Object[] {thirdUser});
      ProofUserManager.getInstance().addUser(secondProof, firstUser);
      assertProofs(firstProof, secondProof, thirdProof, true, false, false, null, new Object[] {secondUser, firstUser}, new Object[] {thirdUser});
      ProofUserManager.getInstance().addUser(thirdProof, firstUser);
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
      Proof fourthProof = new Proof(new Services(AbstractProfile.getDefaultProfile()));
      assertFalse(fourthProof.isDisposed());
      assertEquals(0, ProofUserManager.getInstance().getProofs().length);
      ProofUserManager.getInstance().removeUserAndDispose(fourthProof, new Object());
      assertTrue(fourthProof.isDisposed());
      assertEquals(0, ProofUserManager.getInstance().getProofs().length);
      // Test garbage collection
      Proof fifthProof = new Proof(new Services(AbstractProfile.getDefaultProfile()));
      ProofUserManager.getInstance().addUser(fifthProof, new Object());
      assertProofs(fifthProof);
      fifthProof.dispose();
      fifthProof = null;
      TestUtilsUtil.sleep(1000);
      Runtime.getRuntime().gc();
      TestUtilsUtil.sleep(1000);
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
      if (!ArrayUtil.isEmpty(expectedFirstProofUsers)) {
         expectedCount++;
         assertTrue(ArrayUtil.contains(registeredProofs, firstProof));
         assertUser(firstProof, expectedFirstProofUsers);
      }
      if (!ArrayUtil.isEmpty(expectedSecondProofUsers)) {
         expectedCount++;
         assertTrue(ArrayUtil.contains(registeredProofs, secondProof));
         assertUser(secondProof, expectedSecondProofUsers);
      }
      if (!ArrayUtil.isEmpty(expectedThirdProofUsers)) {
         expectedCount++;
         assertTrue(ArrayUtil.contains(registeredProofs, thirdProof));
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
         assertTrue(ArrayUtil.contains(users, user));
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
         assertTrue(ArrayUtil.contains(proofs, proof));
      }
   }

   /**
    * Tests {@link ProofUserManager#getInstance()}.
    */
   @Test
   public void testGetInstance() {
      ProofUserManager first = ProofUserManager.getInstance();
      assertNotNull(first);
      ProofUserManager second = ProofUserManager.getInstance();
      assertSame(first, second);
   }
}
