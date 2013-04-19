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

package org.key_project.util.test.testcase;

import java.util.List;
import java.util.Map;

import junit.framework.TestCase;

import org.eclipse.core.runtime.IStatus;
import org.junit.Test;
import org.key_project.util.eclipse.Logger;
import org.key_project.util.test.Activator;
import org.key_project.util.test.util.LogLogger;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link Logger}
 * @author Martin Hentschel
 */
public class LoggerTest extends TestCase {
   /**
    * Tests {@link Logger#createErrorStatus(String)}
    */
   @Test
   public void testCreateErrorStatus_String() {
      IStatus status = TestUtilsUtil.createLogger().createErrorStatus("The message");
      assertNotNull(status);
      assertNotNull(status.getChildren());
      assertEquals(0, status.getChildren().length);
      assertEquals(0, status.getCode());
      assertEquals(null, status.getException());
      assertEquals("The message", status.getMessage());
      assertEquals(Activator.PLUGIN_ID, status.getPlugin());
      assertEquals(IStatus.ERROR, status.getSeverity());
      assertEquals(false, status.isMultiStatus());
      assertEquals(false, status.isOK());
   }
   
   /**
    * Tests {@link Logger#createErrorStatus(Throwable)}
    */
   @Test
   public void testCreateErrorStatus_Throwable() {
      Exception exception = new Exception("The message");
      IStatus status = TestUtilsUtil.createLogger().createErrorStatus(exception);
      assertNotNull(status);
      assertNotNull(status.getChildren());
      assertEquals(0, status.getChildren().length);
      assertEquals(0, status.getCode());
      assertEquals(exception, status.getException());
      assertEquals("The message", status.getMessage());
      assertEquals(Activator.PLUGIN_ID, status.getPlugin());
      assertEquals(IStatus.ERROR, status.getSeverity());
      assertEquals(false, status.isMultiStatus());
      assertEquals(false, status.isOK());
   }
   
   /**
    * Tests {@link Logger#createErrorStatus(String, Throwable)}
    */
   @Test
   public void testCreateErrorStatus_String_Throwable() {
      Exception exception = new Exception("The message");
      IStatus status = TestUtilsUtil.createLogger().createErrorStatus("Different message", exception);
      assertNotNull(status);
      assertNotNull(status.getChildren());
      assertEquals(0, status.getChildren().length);
      assertEquals(0, status.getCode());
      assertEquals(exception, status.getException());
      assertEquals("Different message", status.getMessage());
      assertEquals(Activator.PLUGIN_ID, status.getPlugin());
      assertEquals(IStatus.ERROR, status.getSeverity());
      assertEquals(false, status.isMultiStatus());
      assertEquals(false, status.isOK());
   }
   
   /**
    * Tests {@link Logger#logError(String)}
    */
   @Test
   public void testLogError_String() {
      LogLogger logger = new LogLogger();
      try {
         Activator.getDefault().getLog().addLogListener(logger);
         TestUtilsUtil.createLogger().logError("The message");
         Map<String, List<IStatus>> log = logger.getLog();
         assertEquals(1, log.size());
         assertTrue(log.containsKey(Activator.PLUGIN_ID));
         List<IStatus> statusLog = log.get(Activator.PLUGIN_ID);
         assertNotNull(statusLog);
         assertEquals(1, statusLog.size());
         IStatus status = statusLog.get(0);
         assertNotNull(status);
         assertNotNull(status.getChildren());
         assertEquals(0, status.getChildren().length);
         assertEquals(0, status.getCode());
         assertEquals(null, status.getException());
         assertEquals("The message", status.getMessage());
         assertEquals(Activator.PLUGIN_ID, status.getPlugin());
         assertEquals(IStatus.ERROR, status.getSeverity());
         assertEquals(false, status.isMultiStatus());
         assertEquals(false, status.isOK());
      }
      finally {
         Activator.getDefault().getLog().removeLogListener(logger);
      }
   }
   
   /**
    * Tests {@link Logger#logError(String, Throwable)}
    */
   @Test
   public void testLogError_String_Throwable() {
      LogLogger logger = new LogLogger();
      try {
         Activator.getDefault().getLog().addLogListener(logger);
         Exception exception = new Exception("The exception");
         TestUtilsUtil.createLogger().logError("The message", exception);
         Map<String, List<IStatus>> log = logger.getLog();
         assertEquals(1, log.size());
         assertTrue(log.containsKey(Activator.PLUGIN_ID));
         List<IStatus> statusLog = log.get(Activator.PLUGIN_ID);
         assertNotNull(statusLog);
         assertEquals(1, statusLog.size());
         IStatus status = statusLog.get(0);
         assertNotNull(status);
         assertNotNull(status.getChildren());
         assertEquals(0, status.getChildren().length);
         assertEquals(0, status.getCode());
         assertEquals(exception, status.getException());
         assertEquals("The message", status.getMessage());
         assertEquals(Activator.PLUGIN_ID, status.getPlugin());
         assertEquals(IStatus.ERROR, status.getSeverity());
         assertEquals(false, status.isMultiStatus());
         assertEquals(false, status.isOK());
      }
      finally {
         Activator.getDefault().getLog().removeLogListener(logger);
      }
   }
   
   /**
    * Tests {@link Logger#logError(Throwable)}
    */
   @Test
   public void testLogError_Throwable() {
      LogLogger logger = new LogLogger();
      try {
         Activator.getDefault().getLog().addLogListener(logger);
         Exception exception = new Exception("The message");
         TestUtilsUtil.createLogger().logError(exception);
         Map<String, List<IStatus>> log = logger.getLog();
         assertEquals(1, log.size());
         assertTrue(log.containsKey(Activator.PLUGIN_ID));
         List<IStatus> statusLog = log.get(Activator.PLUGIN_ID);
         assertNotNull(statusLog);
         assertEquals(1, statusLog.size());
         IStatus status = statusLog.get(0);
         assertNotNull(status);
         assertNotNull(status.getChildren());
         assertEquals(0, status.getChildren().length);
         assertEquals(0, status.getCode());
         assertEquals(exception, status.getException());
         assertEquals("The message", status.getMessage());
         assertEquals(Activator.PLUGIN_ID, status.getPlugin());
         assertEquals(IStatus.ERROR, status.getSeverity());
         assertEquals(false, status.isMultiStatus());
         assertEquals(false, status.isOK());
      }
      finally {
         Activator.getDefault().getLog().removeLogListener(logger);
      }
   }
   
   /**
    * Tests {@link Logger#logWarning(String)}
    */
   @Test
   public void testLogWarning() {
      LogLogger logger = new LogLogger();
      try {
         Activator.getDefault().getLog().addLogListener(logger);
         TestUtilsUtil.createLogger().logWarning("The warning message");
         Map<String, List<IStatus>> log = logger.getLog();
         assertEquals(1, log.size());
         assertTrue(log.containsKey(Activator.PLUGIN_ID));
         List<IStatus> statusLog = log.get(Activator.PLUGIN_ID);
         assertNotNull(statusLog);
         assertEquals(1, statusLog.size());
         IStatus status = statusLog.get(0);
         assertNotNull(status);
         assertNotNull(status.getChildren());
         assertEquals(0, status.getChildren().length);
         assertEquals(0, status.getCode());
         assertEquals(null, status.getException());
         assertEquals("The warning message", status.getMessage());
         assertEquals(Activator.PLUGIN_ID, status.getPlugin());
         assertEquals(IStatus.WARNING, status.getSeverity());
         assertEquals(false, status.isMultiStatus());
         assertEquals(false, status.isOK());
      }
      finally {
         Activator.getDefault().getLog().removeLogListener(logger);
      }
   }
}