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

package org.key_project.key4eclipse.common.ui.test.testcase;

import org.junit.Test;
import org.key_project.key4eclipse.common.ui.starter.IFileStarter;
import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;
import org.key_project.key4eclipse.common.ui.starter.IProjectStarter;
import org.key_project.key4eclipse.common.ui.starter.IProofStarter;
import org.key_project.key4eclipse.common.ui.test.starter.FirstLoggingFileStarter;
import org.key_project.key4eclipse.common.ui.test.starter.FirstLoggingGlobalStarter;
import org.key_project.key4eclipse.common.ui.test.starter.FirstLoggingMethodStarter;
import org.key_project.key4eclipse.common.ui.test.starter.FirstLoggingProjectStarter;
import org.key_project.key4eclipse.common.ui.test.starter.FirstLoggingProofStarter;
import org.key_project.key4eclipse.common.ui.test.starter.SecondLoggingFileStarter;
import org.key_project.key4eclipse.common.ui.test.starter.SecondLoggingGlobalStarter;
import org.key_project.key4eclipse.common.ui.test.starter.SecondLoggingMethodStarter;
import org.key_project.key4eclipse.common.ui.test.starter.SecondLoggingProjectStarter;
import org.key_project.key4eclipse.common.ui.test.starter.SecondLoggingProofStarter;
import org.key_project.key4eclipse.common.ui.util.StarterDescription;
import org.key_project.key4eclipse.common.ui.util.StarterPreferenceUtil;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;

/**
 * Tests for {@link StarterUtil}.
 * @author Martin Hentschel
 */
public class StarterUtilTest extends AbstractSetupTestCase {
   /**
    * Tests {@link StarterUtil#areProofStartersAvailable()}
    */
   @Test
   public void testAreProofStartersAvailable() throws Exception {
      boolean originalDisabled = StarterPreferenceUtil.isProofStarterDisabled();
      ImmutableList<StarterDescription<IProofStarter>> starters = StarterUtil.getProofStarters();
      try {
         // Make sure that starters are available
         StarterPreferenceUtil.setProofStarterDisabled(false);
         assertTrue(StarterUtil.areProofStartersAvailable());
         // Disable starters
         StarterPreferenceUtil.setProofStarterDisabled(true);
         assertFalse(StarterUtil.areProofStartersAvailable());
         // Enable starters
         StarterPreferenceUtil.setProofStarterDisabled(false);
         assertTrue(StarterUtil.areProofStartersAvailable());
         // Remove all starters
         ObjectUtil.set(null, StarterUtil.class, "proofStarters", ImmutableSLList.nil());
         assertFalse(StarterUtil.areProofStartersAvailable());
      }
      finally {
         StarterPreferenceUtil.setProofStarterDisabled(originalDisabled);
         ObjectUtil.set(null, StarterUtil.class, "proofStarters", starters);
      }
   }
   
   /**
    * Tests {@link StarterUtil#areProjectStartersAvailable()}
    */
   @Test
   public void testAreProjectStartersAvailable() throws Exception {
      boolean originalDisabled = StarterPreferenceUtil.isProjectStarterDisabled();
      ImmutableList<StarterDescription<IProjectStarter>> starters = StarterUtil.getProjectStarters();
      try {
         // Make sure that starters are available
         StarterPreferenceUtil.setProjectStarterDisabled(false);
         assertTrue(StarterUtil.areProjectStartersAvailable());
         // Disable starters
         StarterPreferenceUtil.setProjectStarterDisabled(true);
         assertFalse(StarterUtil.areProjectStartersAvailable());
         // Enable starters
         StarterPreferenceUtil.setProjectStarterDisabled(false);
         assertTrue(StarterUtil.areProjectStartersAvailable());
         // Remove all starters
         ObjectUtil.set(null, StarterUtil.class, "projectStarters", ImmutableSLList.nil());
         assertFalse(StarterUtil.areProjectStartersAvailable());
      }
      finally {
         StarterPreferenceUtil.setProjectStarterDisabled(originalDisabled);
         ObjectUtil.set(null, StarterUtil.class, "projectStarters", starters);
      }
   }

   /**
    * Tests {@link StarterUtil#areFileStartersAvailable()}
    */
   @Test
   public void testAreFileStartersAvailable() throws Exception {
      boolean originalDisabled = StarterPreferenceUtil.isFileStarterDisabled();
      ImmutableList<StarterDescription<IFileStarter>> starters = StarterUtil.getFileStarters();
      try {
         // Make sure that starters are available
         StarterPreferenceUtil.setFileStarterDisabled(false);
         assertTrue(StarterUtil.areFileStartersAvailable());
         // Disable starters
         StarterPreferenceUtil.setFileStarterDisabled(true);
         assertFalse(StarterUtil.areFileStartersAvailable());
         // Enable starters
         StarterPreferenceUtil.setFileStarterDisabled(false);
         assertTrue(StarterUtil.areFileStartersAvailable());
         // Remove all starters
         ObjectUtil.set(null, StarterUtil.class, "fileStarters", ImmutableSLList.nil());
         assertFalse(StarterUtil.areFileStartersAvailable());
      }
      finally {
         StarterPreferenceUtil.setFileStarterDisabled(originalDisabled);
         ObjectUtil.set(null, StarterUtil.class, "fileStarters", starters);
      }
   }

   /**
    * Tests {@link StarterUtil#areMethodStartersAvailable()}
    */
   @Test
   public void testAreMethodStartersAvailable() throws Exception {
      boolean originalDisabled = StarterPreferenceUtil.isMethodStarterDisabled();
      ImmutableList<StarterDescription<IMethodStarter>> starters = StarterUtil.getMethodStarters();
      try {
         // Make sure that starters are available
         StarterPreferenceUtil.setMethodStarterDisabled(false);
         assertTrue(StarterUtil.areMethodStartersAvailable());
         // Disable starters
         StarterPreferenceUtil.setMethodStarterDisabled(true);
         assertFalse(StarterUtil.areMethodStartersAvailable());
         // Enable starters
         StarterPreferenceUtil.setMethodStarterDisabled(false);
         assertTrue(StarterUtil.areMethodStartersAvailable());
         // Remove all starters
         ObjectUtil.set(null, StarterUtil.class, "methodStarters", ImmutableSLList.nil());
         assertFalse(StarterUtil.areMethodStartersAvailable());
      }
      finally {
         StarterPreferenceUtil.setMethodStarterDisabled(originalDisabled);
         ObjectUtil.set(null, StarterUtil.class, "methodStarters", starters);
      }
   }

   /**
    * Tests {@link StarterUtil#areGlobalStartersAvailable()}
    */
   @Test
   public void testAreGlobalStartersAvailable() throws Exception {
      boolean originalDisabled = StarterPreferenceUtil.isGlobalStarterDisabled();
      ImmutableList<StarterDescription<IGlobalStarter>> starters = StarterUtil.getGlobalStarters();
      try {
         // Make sure that starters are available
         StarterPreferenceUtil.setGlobalStarterDisabled(false);
         assertTrue(StarterUtil.areGlobalStartersAvailable());
         // Disable starters
         StarterPreferenceUtil.setGlobalStarterDisabled(true);
         assertFalse(StarterUtil.areGlobalStartersAvailable());
         // Enable starters
         StarterPreferenceUtil.setGlobalStarterDisabled(false);
         assertTrue(StarterUtil.areGlobalStartersAvailable());
         // Remove all starters
         ObjectUtil.set(null, StarterUtil.class, "globalStarters", ImmutableSLList.nil());
         assertFalse(StarterUtil.areGlobalStartersAvailable());
      }
      finally {
         StarterPreferenceUtil.setGlobalStarterDisabled(originalDisabled);
         ObjectUtil.set(null, StarterUtil.class, "globalStarters", starters);
      }
   }
   
   /**
    * Tests {@link StarterUtil#getProofStarters()} and
    * {@link StarterUtil#searchStarter(ImmutableList, String)}.
    */
   @Test
   public void testGetProofStarters() {
      // Get starters first time
      ImmutableList<StarterDescription<IProofStarter>> starters = StarterUtil.getProofStarters();
      // Make sure that first test starter is contained
      StarterDescription<IProofStarter> firstStarter = StarterUtil.searchStarter(starters, FirstLoggingProofStarter.ID);
      assertStarterDescription(firstStarter, FirstLoggingProofStarter.ID, FirstLoggingProofStarter.NAME, FirstLoggingProofStarter.class, FirstLoggingProofStarter.DESCRIPTION);
      // Make sure that second test starter is contained
      StarterDescription<IProofStarter> secondStarter = StarterUtil.searchStarter(starters, SecondLoggingProofStarter.ID);
      assertStarterDescription(secondStarter, SecondLoggingProofStarter.ID, SecondLoggingProofStarter.NAME, SecondLoggingProofStarter.class, SecondLoggingProofStarter.DESCRIPTION);
      // Make sure that invalid start is not contained
      assertNull(StarterUtil.searchStarter(starters, "INVALID_STARTER_ID"));
      // Test null search
      assertNull(StarterUtil.searchStarter(starters, null));
      assertNull(StarterUtil.searchStarter(null, "INVALID_STARTER_ID"));
      assertNull(StarterUtil.searchStarter(null, null));
      // Get starters again
      ImmutableList<StarterDescription<IProofStarter>> startersAgain = StarterUtil.getProofStarters();
      assertSame(starters, startersAgain);
   }
   
   /**
    * Tests {@link StarterUtil#getProjectStarters()} and
    * {@link StarterUtil#searchStarter(ImmutableList, String)}.
    */
   @Test
   public void testGetProjectStarters() {
      // Get starters first time
      ImmutableList<StarterDescription<IProjectStarter>> starters = StarterUtil.getProjectStarters();
      // Make sure that first test starter is contained
      StarterDescription<IProjectStarter> firstStarter = StarterUtil.searchStarter(starters, FirstLoggingProjectStarter.ID);
      assertStarterDescription(firstStarter, FirstLoggingProjectStarter.ID, FirstLoggingProjectStarter.NAME, FirstLoggingProjectStarter.class, FirstLoggingProjectStarter.DESCRIPTION);
      // Make sure that second test starter is contained
      StarterDescription<IProjectStarter> secondStarter = StarterUtil.searchStarter(starters, SecondLoggingProjectStarter.ID);
      assertStarterDescription(secondStarter, SecondLoggingProjectStarter.ID, SecondLoggingProjectStarter.NAME, SecondLoggingProjectStarter.class, SecondLoggingProjectStarter.DESCRIPTION);
      // Make sure that invalid start is not contained
      assertNull(StarterUtil.searchStarter(starters, "INVALID_STARTER_ID"));
      // Test null search
      assertNull(StarterUtil.searchStarter(starters, null));
      assertNull(StarterUtil.searchStarter(null, "INVALID_STARTER_ID"));
      assertNull(StarterUtil.searchStarter(null, null));
      // Get starters again
      ImmutableList<StarterDescription<IProjectStarter>> startersAgain = StarterUtil.getProjectStarters();
      assertSame(starters, startersAgain);
   }

   /**
    * Tests {@link StarterUtil#getFileStarters()} and
    * {@link StarterUtil#searchStarter(ImmutableList, String)}.
    */
   @Test
   public void testGetFileStarters() {
      // Get starters first time
      ImmutableList<StarterDescription<IFileStarter>> starters = StarterUtil.getFileStarters();
      // Make sure that first test starter is contained
      StarterDescription<IFileStarter> firstStarter = StarterUtil.searchStarter(starters, FirstLoggingFileStarter.ID);
      assertStarterDescription(firstStarter, FirstLoggingFileStarter.ID, FirstLoggingFileStarter.NAME, FirstLoggingFileStarter.class, FirstLoggingFileStarter.DESCRIPTION);
      // Make sure that second test starter is contained
      StarterDescription<IFileStarter> secondStarter = StarterUtil.searchStarter(starters, SecondLoggingFileStarter.ID);
      assertStarterDescription(secondStarter, SecondLoggingFileStarter.ID, SecondLoggingFileStarter.NAME, SecondLoggingFileStarter.class, SecondLoggingFileStarter.DESCRIPTION);
      // Make sure that invalid start is not contained
      assertNull(StarterUtil.searchStarter(starters, "INVALID_STARTER_ID"));
      // Test null search
      assertNull(StarterUtil.searchStarter(starters, null));
      assertNull(StarterUtil.searchStarter(null, "INVALID_STARTER_ID"));
      assertNull(StarterUtil.searchStarter(null, null));
      // Get starters again
      ImmutableList<StarterDescription<IFileStarter>> startersAgain = StarterUtil.getFileStarters();
      assertSame(starters, startersAgain);
   }

   /**
    * Tests {@link StarterUtil#getMethodStarters()} and
    * {@link StarterUtil#searchStarter(ImmutableList, String)}.
    */
   @Test
   public void testGetMethodStarters() {
      // Get starters first time
      ImmutableList<StarterDescription<IMethodStarter>> starters = StarterUtil.getMethodStarters();
      // Make sure that first test starter is contained
      StarterDescription<IMethodStarter> firstStarter = StarterUtil.searchStarter(starters, FirstLoggingMethodStarter.ID);
      assertStarterDescription(firstStarter, FirstLoggingMethodStarter.ID, FirstLoggingMethodStarter.NAME, FirstLoggingMethodStarter.class, FirstLoggingMethodStarter.DESCRIPTION);
      // Make sure that second test starter is contained
      StarterDescription<IMethodStarter> secondStarter = StarterUtil.searchStarter(starters, SecondLoggingMethodStarter.ID);
      assertStarterDescription(secondStarter, SecondLoggingMethodStarter.ID, SecondLoggingMethodStarter.NAME, SecondLoggingMethodStarter.class, SecondLoggingMethodStarter.DESCRIPTION);
      // Make sure that invalid start is not contained
      assertNull(StarterUtil.searchStarter(starters, "INVALID_STARTER_ID"));
      // Test null search
      assertNull(StarterUtil.searchStarter(starters, null));
      assertNull(StarterUtil.searchStarter(null, "INVALID_STARTER_ID"));
      assertNull(StarterUtil.searchStarter(null, null));
      // Get starters again
      ImmutableList<StarterDescription<IMethodStarter>> startersAgain = StarterUtil.getMethodStarters();
      assertSame(starters, startersAgain);
   }

   /**
    * Tests {@link StarterUtil#getGlobalStarters()} and
    * {@link StarterUtil#searchStarter(ImmutableList, String)}.
    */
   @Test
   public void testGetGlobalStarters() {
      // Get starters first time
      ImmutableList<StarterDescription<IGlobalStarter>> starters = StarterUtil.getGlobalStarters();
      // Make sure that first test starter is contained
      StarterDescription<IGlobalStarter> firstStarter = StarterUtil.searchStarter(starters, FirstLoggingGlobalStarter.ID);
      assertStarterDescription(firstStarter, FirstLoggingGlobalStarter.ID, FirstLoggingGlobalStarter.NAME, FirstLoggingGlobalStarter.class, FirstLoggingGlobalStarter.DESCRIPTION);
      // Make sure that second test starter is contained
      StarterDescription<IGlobalStarter> secondStarter = StarterUtil.searchStarter(starters, SecondLoggingGlobalStarter.ID);
      assertStarterDescription(secondStarter, SecondLoggingGlobalStarter.ID, SecondLoggingGlobalStarter.NAME, SecondLoggingGlobalStarter.class, SecondLoggingGlobalStarter.DESCRIPTION);
      // Make sure that invalid start is not contained
      assertNull(StarterUtil.searchStarter(starters, "INVALID_STARTER_ID"));
      // Test null search
      assertNull(StarterUtil.searchStarter(starters, null));
      assertNull(StarterUtil.searchStarter(null, "INVALID_STARTER_ID"));
      assertNull(StarterUtil.searchStarter(null, null));
      // Get starters again
      ImmutableList<StarterDescription<IGlobalStarter>> startersAgain = StarterUtil.getGlobalStarters();
      assertSame(starters, startersAgain);
   }

   /**
    * Makes sure that the correct {@link StarterDescription} is available.
    * @param currentStarter The current starter.
    * @param expectedId The expected ID.
    * @param expectedName The expected name.
    * @param expectedInstanceClass The expected instance class.
    * @param expectedDescription The expected description.
    */
   protected void assertStarterDescription(StarterDescription<?> currentStarter, 
                                           String expectedId,
                                           String expectedName, 
                                           Class<?> expectedInstanceClass, 
                                           String expectedDescription) {
      assertNotNull(currentStarter);
      assertEquals(expectedId, currentStarter.getId());
      assertEquals(expectedName, currentStarter.getName());
      assertNotNull(currentStarter.getInstance());
      assertEquals(expectedInstanceClass, currentStarter.getInstance().getClass());
      assertEquals(expectedDescription, currentStarter.getDescription());
   }
}