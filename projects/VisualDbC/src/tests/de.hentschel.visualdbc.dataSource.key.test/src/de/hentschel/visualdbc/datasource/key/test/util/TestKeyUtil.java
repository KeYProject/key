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

package de.hentschel.visualdbc.datasource.key.test.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.awt.Component;
import java.io.File;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import javax.swing.JFrame;
import javax.swing.UIManager;
import javax.swing.tree.TreeModel;

import junit.framework.TestCase;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.key_project.key4eclipse.starter.core.job.AbstractKeYMainWindowJob;
import org.key_project.key4eclipse.test.util.TestKeY4EclipseUtil;
import org.key_project.swtbot.swing.bot.AbstractSwingBotComponent;
import org.key_project.swtbot.swing.bot.SwingBot;
import org.key_project.swtbot.swing.bot.SwingBotJButton;
import org.key_project.swtbot.swing.bot.SwingBotJDialog;
import org.key_project.swtbot.swing.bot.SwingBotJFrame;
import org.key_project.swtbot.swing.bot.SwingBotJList;
import org.key_project.swtbot.swing.bot.SwingBotJMenuBar;
import org.key_project.swtbot.swing.bot.SwingBotJTabbedPane;
import org.key_project.swtbot.swing.bot.SwingBotJTree;
import org.key_project.swtbot.swing.bot.finder.waits.Conditions;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.TestUtilsUtil;
import org.key_project.util.test.util.TestUtilsUtil.MethodTreatment;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.model.KeyDriver;
import de.hentschel.visualdbc.datasource.key.model.KeyProof;
import de.hentschel.visualdbc.datasource.key.model.event.IKeYConnectionListener;
import de.hentschel.visualdbc.datasource.key.model.event.KeYConnectionEvent;
import de.hentschel.visualdbc.datasource.key.test.Activator;
import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.event.DSProofEvent;
import de.hentschel.visualdbc.datasource.model.exception.DSCanceledException;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryAttribute;
import de.hentschel.visualdbc.datasource.model.memory.MemoryAxiom;
import de.hentschel.visualdbc.datasource.model.memory.MemoryAxiomContract;
import de.hentschel.visualdbc.datasource.model.memory.MemoryClass;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConnection;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConstructor;
import de.hentschel.visualdbc.datasource.model.memory.MemoryEnum;
import de.hentschel.visualdbc.datasource.model.memory.MemoryEnumLiteral;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInterface;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInvariant;
import de.hentschel.visualdbc.datasource.model.memory.MemoryMethod;
import de.hentschel.visualdbc.datasource.model.memory.MemoryOperation;
import de.hentschel.visualdbc.datasource.model.memory.MemoryOperationContract;
import de.hentschel.visualdbc.datasource.model.memory.MemoryPackage;
import de.hentschel.visualdbc.datasource.test.util.ConnectionLogger;
import de.hentschel.visualdbc.datasource.test.util.TestDataSourceUtil;
import de.hentschel.visualdbc.datasource.util.DriverUtil;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.generation.operation.CreateOperation;
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.hentschel.visualdbc.interactive.proving.ui.test.util.TestInteractiveProvingUtil;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.TaskTreeModel;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * Provides static methods that make testing easier.
 * @author Martin Hentschel
 */
public final class TestKeyUtil {
   /**
    * Forbid instances.
    */
   private TestKeyUtil() {
   }
   
   /**
    * Bug handling that the final flag is not implemented on attributes.
    * @param isFinal The original final flag to use.
    * @return The value to use instead.
    */
   private static boolean bugAttributeFinal(boolean isFinal) {
      return false;
   }

   /**
    * Bug handling that the visibility doesn't work on attributes.
    * @param visibility The original visibility to use.
    * @return The visibility to use instead.
    */
   private static DSVisibility bugAttributeVisibility(DSVisibility visibility) {
      return DSVisibility.DEFAULT;
   }

   /**
    * Bug handling that the visibility doesn't work on enumerations.
    * @param visibility The original visibility to use.
    * @return The visibility to use instead.
    */
   private static DSVisibility bugEnumVisibility(DSVisibility visibility) {
      return DSVisibility.DEFAULT;
   }
   
   /**
    * Bug handling that the visibility doesn't work on inner interfaces.
    * @param visibility The original visibility to use.
    * @return The visibility to use instead.
    */   
   private static DSVisibility bugInnerInterfaceVisibility(DSVisibility visibility) {
      if (DSVisibility.PUBLIC.equals(visibility)) {
         return DSVisibility.PUBLIC;
      }
      else {
         return DSVisibility.DEFAULT;
      }
   }
   
   /**
    * Returns an opened data source connection to the source code analyzed with KeY.
    * @return The opened {@link IDSConnection}.
    * @throws DSException Occurred Exception
    */
   public static KeyConnection createKeyConnection(File location) throws DSException {
      return createKeyConnection(location, null, null);
   }
   
   /**
    * Returns an opened data source connection to the source code analyzed with KeY.
    * @return The opened {@link IDSConnection}.
    * @throws DSException Occurred Exception
    */
   public static KeyConnection createKeyConnection(boolean interactive, 
                                                   File location) throws DSException {
      return createKeyConnection(interactive, location, null, null);
   }
   
   /**
    * Returns an opened data source connection to the source code analyzed with KeY.
    * @return The opened {@link IDSConnection}.
    * @throws DSException Occurred Exception
    */
   public static KeyConnection createKeyConnection(File location,
                                                   DSPackageManagement packageManagement,
                                                   ConnectionLogger logger) throws DSException {
      return createKeyConnection(false, location, packageManagement, logger);
   }
   
   /**
    * Returns an opened data source connection to the source code analyzed with KeY.
    * @return The opened {@link IDSConnection}.
    * @throws DSException Occurred Exception
    */
   public static KeyConnection createKeyConnection(boolean interactive,
                                                   File location,
                                                   DSPackageManagement packageManagement,
                                                   ConnectionLogger logger) throws DSException {
      TestCase.assertNotNull(location);
      TestCase.assertTrue(location.isDirectory());
      Map<String, Object> settings = new HashMap<String, Object>();
      settings.put(KeyDriver.SETTING_LOCATION, location);
      if (packageManagement != null) {
         settings.put(KeyDriver.SETTING_PACKAGE_MANAGEMENT, packageManagement);
      }
      return createKeyConnection(interactive, settings, logger);
   }
   
   /**
    * Returns an opened data source connection to the source code analyzed with KeY.
    * @return The opened {@link IDSConnection}.
    * @throws DSException Occurred Exception
    */
   public static KeyConnection createKeyConnection(Map<String, Object> settings,
                                                   ConnectionLogger logger) throws DSException {
      return createKeyConnection(false, settings, logger);
   }
   
   /**
    * Returns an opened data source connection to the source code analyzed with KeY.
    * @return The opened {@link IDSConnection}.
    * @throws DSException Occurred Exception
    */
   public static KeyConnection createKeyConnection(boolean interactive,
                                                   Map<String, Object> settings,
                                                   ConnectionLogger logger) throws DSException {
      // Get driver
      IDSDriver driver = DriverUtil.getDriver(KeyDriver.ID);
      TestCase.assertNotNull(driver);
      // Create connection
      IDSConnection connection = driver.createConnection();
      TestCase.assertNotNull(connection);
      if (logger != null) {
         TestCase.assertEquals(0, connection.getConnectionListeners().length);
         connection.addConnectionListener(logger);
         TestCase.assertEquals(1, connection.getConnectionListeners().length);
         TestDataSourceUtil.compareConnectionEvents(connection, logger, false, false, false);
      }
      KeYConnectJob job = new KeYConnectJob(interactive, settings, connection);
      job.schedule();
      TestUtilsUtil.waitForJob(job);
      if (job.getException() != null) {
         throw job.getException();
      }
      TestCase.assertTrue(connection.isConnected());
      TestCase.assertEquals(interactive, connection.isInteractive());
      if (logger != null) {
         TestDataSourceUtil.compareConnectionEvents(connection, logger, true, true, false);
      }
      // Make sure that the connection returns the correct connection settings
      TestCase.assertNotNull(connection.getConnectionSettings());
      Set<Entry<String, Object>> expectedEntries = settings.entrySet();
      Set<Entry<String, Object>> currentEntries = connection.getConnectionSettings().entrySet();
      Iterator<Entry<String, Object>> expectedIter = expectedEntries.iterator();
      Iterator<Entry<String, Object>> currentIter = currentEntries.iterator();
      TestCase.assertEquals(expectedEntries.size(), currentEntries.size());
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         Entry<String, Object> expectedNext = expectedIter.next();
         Entry<String, Object> currentNext = currentIter.next();
         TestCase.assertEquals(expectedNext.getKey(), currentNext.getKey());
         TestCase.assertEquals(expectedNext.getValue(), currentNext.getValue());
      }
      TestCase.assertFalse(expectedIter.hasNext());
      TestCase.assertFalse(currentIter.hasNext());
      TestCase.assertTrue(connection instanceof KeyConnection);
      return (KeyConnection)connection;
   }
   
   /**
    * This {@link Job} is used to connect to a KeY data source. It is required
    * because of the SWT and Swing integration which requires asynchronous
    * calls between both UI threads. A required synchronous call is possible
    * via a separate {@link Thread} which is provided by this {@link Job}.
    * @author Martin Hentschel
    */
   private static class KeYConnectJob extends AbstractKeYMainWindowJob {
      /**
       * Use interactive mode?
       */
      private boolean interactive;
      
      /**
       * The connection settings to use.
       */
      private Map<String, Object> settings;
      
      /**
       * The {@link IDSConnection} to connect to.
       */
      private IDSConnection connection;
      
      /**
       * Occurred Exception.
       */
      private DSException exception;
      
      /**
       * Constructor.
       * @param interactive  Use interactive mode?
       * @param settings The connection settings to use.
       * @param connection The {@link IDSConnection} to connect to.
       */
      public KeYConnectJob(boolean interactive,
                           Map<String, Object> settings,
                           IDSConnection connection) {
         super("Connecting to KeY");
         this.interactive = interactive;
         this.settings = settings;
         this.connection = connection;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected IStatus run(IProgressMonitor monitor) {
         try {
            connection.connect(settings, interactive, new NullProgressMonitor());
            return Status.OK_STATUS;
         }
         catch (DSException e) {
            this.exception = e;
            return new Status(IStatus.ERROR, Activator.PLUGIN_ID, e.getMessage(), e);
         }
      }

      /**
       * Returns the occurred exception.
       * @return The occurred exception or {@code null} if no one occurred.
       */
      public DSException getException() {
         return exception;
      }
   }

   /**
    * Creates the expected model for the paycard example.
    * @return The expected model.
    */
   public static IDSConnection createExpectedQuicktourModel() {
      MemoryConnection con = new MemoryConnection();
      MemoryPackage paycard = new MemoryPackage("paycard");
      con.addPackage(paycard);
      MemoryClass cardException = createCardException("CardException");
      paycard.addClass(cardException);
      MemoryClass logFile = createLogFile("LogFile", "paycard.LogFile", "paycard.LogRecord", new String[] {"0", "1", "2"}, new String[] {"0", "2", "0"});
      paycard.addClass(logFile);
      MemoryClass logRecord = createLogRecord("LogRecord", "paycard.LogRecord", new String[] {"4", "6"}, new String[] {"0", "0", "0", "0", "7"});
      paycard.addClass(logRecord);
      MemoryClass payCard = createPayCard("PayCard", "paycard.PayCard", "paycard.LogFile", new String[] {"8", "9", "11", "13"}, new String[] {"0", "0", "1", "0", "0", "0", "0"});
      paycard.addClass(payCard);
      return con;
   }

   /**
    * Creates the expected model for the package example with
    * {@link DSPackageManagement#NO_PACKAGES}
    * @return The expected model.
    */   
   public static IDSConnection createExpectedPackageTestModel_NoPackages() {
      MemoryConnection con = new MemoryConnection();
      MemoryClass payCard = createPayCard("PayCard", "PayCard", "packageA.LogFile", new String[] {"0", "1", "3", "5"}, new String[] {"0", "0", "1", "0", "0", "0", "0"});
      con.addClass(payCard);
      MemoryClass logFile = createLogFile("packageA.LogFile", "packageA.LogFile", "packageB.p1.LogRecord", new String[] {"7", "8", "9"}, new String[] {"0", "8", "0"});
      con.addClass(logFile);
      MemoryClass logRecord = createLogRecord("packageB.p1.LogRecord", "packageB.p1.LogRecord", new String[] {"11", "13"}, new String[] {"0", "0", "0", "0", "13"});
      con.addClass(logRecord);
      MemoryClass cardException = createCardException("packageB.p2.p2a.CardException");
      con.addClass(cardException);
      return con;
   }

   /**
    * Creates the expected model for the package example with
    * {@link DSPackageManagement#FLAT_LIST}
    * @return The expected model.
    */   
   public static IDSConnection createExpectedPackageTestModel_FlatList() {
      MemoryConnection con = new MemoryConnection();
      MemoryClass payCard = createPayCard("PayCard", "PayCard", "packageA.LogFile", new String[] {"0", "1", "3", "5"}, new String[] {"0", "0", "1", "0", "0", "0", "0"});
      con.addClass(payCard);
      MemoryPackage packageA = new MemoryPackage("packageA");
      con.addPackage(packageA);
      MemoryClass logFile = createLogFile("LogFile", "packageA.LogFile", "packageB.p1.LogRecord", new String[] {"7", "8", "9"}, new String[] {"0", "8", "0"});
      packageA.addClass(logFile);
      MemoryPackage packageB_p1 = new MemoryPackage("packageB.p1");
      con.addPackage(packageB_p1);
      MemoryClass logRecord = createLogRecord("LogRecord", "packageB.p1.LogRecord", new String[] {"11", "13"}, new String[] {"0", "0", "0", "0", "13"});
      packageB_p1.addClass(logRecord);
      MemoryPackage packageB_p2_p2a = new MemoryPackage("packageB.p2.p2a");
      con.addPackage(packageB_p2_p2a);
      MemoryClass cardException = createCardException("CardException");
      packageB_p2_p2a.addClass(cardException);
      return con;
   }

   /**
    * Creates the expected model for the package example with
    * {@link DSPackageManagement#HIERARCHY}
    * @return The expected model.
    */   
   public static IDSConnection createExpectedPackageTestModel_Hierarchy() {
      MemoryConnection con = new MemoryConnection();
      MemoryClass payCard = createPayCard("PayCard", "PayCard", "packageA.LogFile", new String[] {"0", "1", "3", "5"}, new String[] {"0", "0", "1", "0", "0", "0", "0"});
      con.addClass(payCard);
      MemoryPackage packageA = new MemoryPackage("packageA");
      con.addPackage(packageA);
      MemoryClass logFile = createLogFile("LogFile", "packageA.LogFile", "packageB.p1.LogRecord", new String[] {"7", "8", "9"}, new String[] {"0", "8", "0"});
      packageA.addClass(logFile);
      MemoryPackage packageB = new MemoryPackage("packageB");
      con.addPackage(packageB);
      MemoryPackage packageB_p1 = new MemoryPackage("p1");
      packageB.addPackage(packageB_p1);
      MemoryClass logRecord = createLogRecord("LogRecord", "packageB.p1.LogRecord", new String[] {"11", "13"}, new String[] {"0", "0", "0", "0", "13"});
      packageB_p1.addClass(logRecord);
      MemoryPackage packageB_p2 = new MemoryPackage("p2");
      packageB.addPackage(packageB_p2);
      MemoryPackage packageB_p2_p2a = new MemoryPackage("p2a");
      packageB_p2.addPackage(packageB_p2_p2a);
      MemoryClass cardException = createCardException("CardException");
      packageB_p2_p2a.addClass(cardException);
      return con;
   }
   
   /**
    * Creates the class "CardException".
    * @param className The name to use.
    * @return The created {@link IDSClass}.
    */
   protected static MemoryClass createCardException(String className) {
      MemoryClass result = new MemoryClass(className, DSVisibility.PUBLIC);
      MemoryConstructor constructor = new MemoryConstructor("CardException()", DSVisibility.PUBLIC);
      addOperationObligations(constructor, true, false, true);
      result.addConstructor(constructor);
      result.getExtendsFullnames().add("java.lang.Exception");
      return result;
   }
   
   /**
    * Adds the selected obligations to the {@link MemoryOperation}.
    * @param o The {@link MemoryOperation} to fill.
    * @param preservesInv Add preserves inv?
    * @param preservesOwnInv Add preserves own inv?
    * @param preservesGuard Add preserves guard?
    */
   protected static void addOperationObligations(MemoryOperation o, boolean preservesInv, boolean preservesOwnInv, boolean preservesGuard) {
   }
   
   /**
    * Adds all operation contract obligations to the {@link MemoryOperationContract}.
    * @param oc The {@link MemoryOperationContract} to fill.
    */
   protected static void addAllOperationContractObligations(MemoryOperationContract oc) {
      oc.getObligations().add(KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT);
   }
  
   /**
    * Adds all operation contract obligations to the {@link MemoryAxiomContract}.
    * @param oc The {@link MemoryAxiomContract} to fill.
    */
   protected static void addAllOperationContractObligations(MemoryAxiomContract ac) {
      ac.getObligations().add(KeyConnection.PROOF_OBLIGATION_OPERATION_CONTRACT);
   }

   /**
    * Creates the class "LogRecord".
    * @param className The name to use.
    * @param logRecordFullqualifiedName The full qualified name.
    * @param invariantIds The invariant ids.
    * @param operationContractIds The operation contract ids.
    * @return The created {@link IDSClass}.
    */
   protected static MemoryClass createLogRecord(String className,
                                                String logRecordFullqualifiedName,
                                                String[] invariantIds,
                                                String[] operationContractIds) {
      MemoryClass result = new MemoryClass(className, DSVisibility.PUBLIC);
      MemoryConstructor constructor = new MemoryConstructor("LogRecord()", DSVisibility.PUBLIC);
      addOperationObligations(constructor, true, true, true);
      result.addConstructor(constructor);
      MemoryMethod setRecord = new MemoryMethod("setRecord(balance : int)", "void", DSVisibility.PUBLIC);
      addOperationObligations(setRecord, true, true, true);
      MemoryOperationContract sr = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId(logRecordFullqualifiedName, logRecordFullqualifiedName, "setRecord(int)", operationContractIds[0], "normal_behavior"),
                                                               "balance >= 0 & self.<inv>", 
                                                               "self.balance = balance\n" +
                                                               "&   self.transactionId\n" +
                                                               "  = heapAtPre[" + logRecordFullqualifiedName + ".transactionCounter]\n" +
                                                               "& self.<inv>\n" +
                                                               "& exc = null", 
                                                               "mod[heap]:           {(self, empty)} \\cup {(self, balance)}\n" +
                                                               "     \\cup {(self, transactionId)}\n" +
                                                               "\\cup {(null, transactionCounter)}", 
                                                               "diamond");
      addAllOperationContractObligations(sr);
      setRecord.addOperationContract(sr);
      result.addMethod(setRecord);
      MemoryMethod getBalance = new MemoryMethod("getBalance()", "int", DSVisibility.PUBLIC);
      addOperationObligations(getBalance, true, true, true);
      MemoryOperationContract gb2 = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId(logRecordFullqualifiedName, logRecordFullqualifiedName, "getBalance()", operationContractIds[2], "normal_behavior"),
                                                                "self.<inv>", 
                                                                "result = self.balance & self.<inv> & exc = null", 
                                                                "mod[heap]: {}", 
                                                                "diamond");
      addAllOperationContractObligations(gb2);
      getBalance.addOperationContract(gb2);
      result.addMethod(getBalance);
      MemoryMethod getTransactionId = new MemoryMethod("getTransactionId()", "int", DSVisibility.PUBLIC);
      addOperationObligations(getTransactionId, true, true, true);
      MemoryOperationContract gti2 = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId(logRecordFullqualifiedName, logRecordFullqualifiedName, "getTransactionId()", operationContractIds[3], "normal_behavior"),
                                                                 "self.<inv>", 
                                                                 "result = self.transactionId & self.<inv> & exc = null", 
                                                                 "mod[heap]: {}", 
                                                                 "diamond");
      addAllOperationContractObligations(gti2);
      getTransactionId.addOperationContract(gti2);
      result.addMethod(getTransactionId);
      result.addAttribute(new MemoryAttribute("transactionCounter", "int", bugAttributeVisibility(DSVisibility.PRIVATE), true));
      result.addAttribute(new MemoryAttribute("balance", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      result.addAttribute(new MemoryAttribute("transactionId", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      result.addAttribute(new MemoryAttribute("empty", "boolean", bugAttributeVisibility(DSVisibility.PRIVATE)));
      result.getExtendsFullnames().add("java.lang.Object");
      result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantIds[0] + " in LogRecord", "!self.empty = TRUE\n" +
      		                                                                                                 "-> self.balance >= 0 & self.transactionId >= 0"));
      result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantIds[1] + " in LogRecord", logRecordFullqualifiedName + ".transactionCounter >= 0"));
      return result;
   }

   /**
    * Creates the class "PayCard".
    * @param className The name to use.
    * @param qualifiedPaycardName The qualified name of the class "PayCard".
    * @param qualifiedLogFileName The qualified name of the class "LogFile".
    * @param invariantIDs The IDs of the invariants.
    * @param operationContractIDs The IDs of the operation contracts.
    * @return The created {@link IDSClass}.
    */
   protected static MemoryClass createPayCard(String className, 
                                              String qualifiedPaycardName, 
                                              String qualifiedLogFileName,
                                              String[] invariantIDs,
                                              String[] operationContractIDs) {
      MemoryClass result = new MemoryClass(className, DSVisibility.PUBLIC);
      MemoryConstructor constructorInt = new MemoryConstructor("PayCard(limit : int)", DSVisibility.PUBLIC);
      addOperationObligations(constructorInt, true, true, true);
      result.addConstructor(constructorInt);
      MemoryConstructor constructor = new MemoryConstructor("PayCard()", DSVisibility.PUBLIC);
      addOperationObligations(constructor, true, true, true);
      result.addConstructor(constructor);
      MemoryMethod createJuniorCard = new MemoryMethod("createJuniorCard()", qualifiedPaycardName, DSVisibility.PUBLIC, true);
      addOperationObligations(createJuniorCard, true, true, true);
      MemoryOperationContract cjc = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId(qualifiedPaycardName, qualifiedPaycardName, "createJuniorCard()", operationContractIDs[0], ""), 
                                                                "true", 
                                                                "(exc = null -> result.limit = 100 & !result = null)\n" +
                                                                "& exc = null", 
                                                                "mod[heap]: allLocs", 
                                                                "diamond");
      addAllOperationContractObligations(cjc);
      createJuniorCard.addOperationContract(cjc);
      result.addMethod(createJuniorCard);
      MemoryMethod charge = new MemoryMethod("charge(amount : int)", "boolean", DSVisibility.PUBLIC);
      addOperationObligations(charge, true, true, true);
      MemoryOperationContract c1 = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId(qualifiedPaycardName, qualifiedPaycardName, "charge(int)", operationContractIDs[1], "exceptional_behavior"), 
                                                               "amount <= 0 & self.<inv>", 
                                                               "!exc = null\n" +
                                                               "& (  (   java.lang.Exception::instance(exc) = TRUE\n" +
                                                               "      -> self.<inv>)\n" +
                                                               "   &   java.lang.IllegalArgumentException::instance(exc)\n" +
                                                               "     = TRUE)", 
                                                               "mod[heap]: allLocs", 
                                                               "diamond");
      addAllOperationContractObligations(c1);
      MemoryOperationContract c2 = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId(qualifiedPaycardName, qualifiedPaycardName, "charge(int)", operationContractIDs[2], "normal_behavior"),
                                                               "(  javaAddInt(amount, self.balance) >= self.limit\n" +
                                                               "   | !self.isValid() = TRUE)\n" +
                                                               "& (amount >  0 & self.<inv>)", 
                                                               "!result = TRUE\n" +
                                                               "& (    self.unsuccessfulOperations\n" +
                                                               "     = javaAddInt(heapAtPre[self.unsuccessfulOperations],\n" +
                                                               "                  1)\n" +
                                                               "   & self.<inv>)\n" +
                                                               "& exc = null", 
                                                               "mod[heap]: {(self, unsuccessfulOperations)}", 
                                                               "diamond");
      addAllOperationContractObligations(c2);
      MemoryOperationContract c3 = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId(qualifiedPaycardName, qualifiedPaycardName, "charge(int)", operationContractIDs[3], "normal_behavior"),
                                                               "javaAddInt(amount, self.balance) < self.limit\n" +
                                                               "& self.isValid() = TRUE\n" +
                                                               "& (amount >  0 & self.<inv>)", 
                                                               "result = TRUE\n" +
                                                               "& (    self.balance\n" +
                                                               "     = javaAddInt(amount, heapAtPre[self.balance])\n" +
                                                               "   & self.<inv>)\n" +
                                                               "& exc = null", 
                                                               "mod[heap]: {(self, balance)}", 
                                                               "diamond");
      addAllOperationContractObligations(c3);
      charge.addOperationContract(c1);
      charge.addOperationContract(c2);
      charge.addOperationContract(c3);
      result.addMethod(charge);
      MemoryMethod chargeAndRecord = new MemoryMethod("chargeAndRecord(amount : int)", "void", DSVisibility.PUBLIC);
      addOperationObligations(chargeAndRecord, true, true, true);
      MemoryOperationContract car = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId(qualifiedPaycardName, qualifiedPaycardName, "chargeAndRecord(int)", operationContractIDs[4], "normal_behavior"), 
                                                                "amount >  0 & self.<inv>", 
                                                                "self.balance >= heapAtPre[self.balance]\n" +
                                                                "& self.<inv>\n" +
                                                                "& exc = null", 
                                                                "mod[heap]: allLocs \\setMinus freshLocs(heap)", 
                                                                "diamond");
      addAllOperationContractObligations(car);
      chargeAndRecord.addOperationContract(car);
      result.addMethod(chargeAndRecord);
      MemoryMethod isValid = new MemoryMethod("isValid()", "boolean", DSVisibility.PUBLIC);
      addOperationObligations(isValid, true, true, true);
      MemoryOperationContract iv2 = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId(qualifiedPaycardName, qualifiedPaycardName, "isValid()", operationContractIDs[6], "normal_behavior"), 
                                                                "self.<inv>", 
                                                                "(result = TRUE <-> self.unsuccessfulOperations <= 3)\n" +
                                                                "& self.<inv>\n" +
                                                                "& exc = null", 
                                                                "mod[heap]: {}", 
                                                                "diamond");
      addAllOperationContractObligations(iv2);
      isValid.addOperationContract(iv2);
      result.addMethod(isValid);
      MemoryMethod infoCardMsg = new MemoryMethod("infoCardMsg()", "java.lang.String", DSVisibility.PUBLIC);
      addOperationObligations(infoCardMsg, true, true, true);
      result.addMethod(infoCardMsg);
      result.addAttribute(new MemoryAttribute("limit", "int", bugAttributeVisibility(DSVisibility.DEFAULT)));
      result.addAttribute(new MemoryAttribute("unsuccessfulOperations", "int", bugAttributeVisibility(DSVisibility.DEFAULT)));
      result.addAttribute(new MemoryAttribute("id", "int", bugAttributeVisibility(DSVisibility.DEFAULT)));
      result.addAttribute(new MemoryAttribute("balance", "int", bugAttributeVisibility(DSVisibility.DEFAULT)));
      result.addAttribute(new MemoryAttribute("log", qualifiedLogFileName, bugAttributeVisibility(DSVisibility.PROTECTED)));
      result.getExtendsFullnames().add("java.lang.Object");
      result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantIDs[0] + " in PayCard", "!self.log = null"));
      result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantIDs[1] + " in PayCard", "self.balance >= 0"));
      result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantIDs[2] + " in PayCard", "self.limit >  0"));
      result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantIDs[3] + " in PayCard", "self.unsuccessfulOperations >= 0"));
      return result;
   }
   
   /**
    * Creates the class "LogFile".
    * @param className The name to use.
    * @param qualifiedLogFileClass The full qualified class name.
    * @param qualifiedLogRecordClass The qualified name of the class "LogRecord".
    * @param invariantIds The invariant ids.
    * @param operationContractIds The operation contract ids.
    * @return The created {@link IDSClass}.
    */
   protected static MemoryClass createLogFile(String className, 
                                              String qualifiedLogFileClass,
                                              String qualifiedLogRecordClass,
                                              String[] invariantIds,
                                              String[] operationContractIds) {
      MemoryClass result = new MemoryClass(className, DSVisibility.PUBLIC);
      MemoryConstructor constructor = new MemoryConstructor("LogFile()", DSVisibility.PUBLIC);
      addOperationObligations(constructor, true, true, true);
      result.addConstructor(constructor);
      MemoryMethod addRecord = new MemoryMethod("addRecord(balance : int)", "void", DSVisibility.PUBLIC);
      addOperationObligations(addRecord, true, true, true);
      MemoryOperationContract ar1 = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId(qualifiedLogFileClass, qualifiedLogFileClass, "addRecord(int)", operationContractIds[0], "normal_behavior"),
                                                                "balance >= 0 & self.<inv>", 
                                                                "\\if (!  javaAddInt(heapAtPre[self.currentRecord], 1)\n" +
                                                                "        = " + qualifiedLogFileClass + ".logFileSize)\n" +
                                                                "      \\then (  self.currentRecord\n" +
                                                                "             = javaAddInt(heapAtPre[self.currentRecord],\n" +
                                                                "                          1))\n" +
                                                                "      \\else (self.currentRecord = 0)\n" +
                                                                "& (    self.logArray[self.currentRecord].balance\n" +
                                                                "     = balance\n" +
                                                                "   & self.<inv>)\n" +
                                                                "& exc = null", 
                                                                "mod[heap]: allLocs", 
                                                                "diamond");
      addAllOperationContractObligations(ar1);
      addRecord.addOperationContract(ar1);
      result.addMethod(addRecord);
      MemoryMethod getMaximumRecord = new MemoryMethod("getMaximumRecord()", qualifiedLogRecordClass, DSVisibility.PUBLIC);
      addOperationObligations(getMaximumRecord, true, true, true);
      MemoryOperationContract mr2 = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId(qualifiedLogFileClass, qualifiedLogFileClass, "getMaximumRecord()", operationContractIds[2], "normal_behavior"), 
                                                                "self.<inv>", 
                                                                "\\forall int i;\n" +
                                                                "    (   0 <= i & i < self.logArray.length & inInt(i)\n" +
                                                                "     -> self.logArray[i].balance <= result.balance)\n" +
                                                                "& (self.<inv> & !result = null)\n" +
                                                                "& exc = null", 
                                                                "mod[heap]: {}", 
                                                                "box");
      addAllOperationContractObligations(mr2);
      getMaximumRecord.addOperationContract(mr2);
      result.addMethod(getMaximumRecord);
      result.addAttribute(new MemoryAttribute("logFileSize", "int", bugAttributeVisibility(DSVisibility.PRIVATE), true));
      result.addAttribute(new MemoryAttribute("currentRecord", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      result.addAttribute(new MemoryAttribute("logArray", qualifiedLogRecordClass + KeyConnection.ARRAY_DECLARATION, bugAttributeVisibility(DSVisibility.PRIVATE)));
      result.getExtendsFullnames().add("java.lang.Object");
      result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantIds[0] + " in LogFile", "\\forall int i;\n" +
      		                                                                                               "  (   0 <= i & i < self.logArray.length & inInt(i)\n" +
      		                                                                                               "   -> !self.logArray[i] = null)"));
      result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantIds[1] + " in LogFile", "!self.logArray = null"));
      result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantIds[2] + " in LogFile", "self.logArray.length = " + qualifiedLogFileClass + ".logFileSize\n" +
                                                                                                           "& (  self.currentRecord < " + qualifiedLogFileClass + ".logFileSize\n" +
                                                                                                           "   & (  self.currentRecord >= 0\n" +
                                                                                                           "      & (  !self.logArray = null\n" +
                                                                                                           "         & \\forall int i;\n" +
                                                                                                           "             (   0 <= i & i < self.logArray.length\n" +
                                                                                                           "              -> !self.logArray[i] = null))))"));
      return result;
   }

   /**
    * Creates the expected model for the method and constructor example with
    * {@link DSPackageManagement#FLAT_LIST}
    * @return The expected model.
    */
   public static IDSConnection createExpectedMehtodAndConstructorTestModel() {
      MemoryConnection con = new MemoryConnection();
      MemoryClass methodsAndConstructors = new MemoryClass("MethodsAndConstructors", DSVisibility.PUBLIC, true);
      con.addClass(methodsAndConstructors);
      MemoryConstructor constructor = new MemoryConstructor("MethodsAndConstructors()", DSVisibility.PUBLIC);
      addOperationObligations(constructor, true, false, true);
      methodsAndConstructors.addConstructor(constructor);
      MemoryConstructor constructorMyClass = new MemoryConstructor("MethodsAndConstructors(c : MyClass)", DSVisibility.PUBLIC);
      addOperationObligations(constructorMyClass, true, false, true);
      methodsAndConstructors.addConstructor(constructorMyClass);
      MemoryConstructor constructorInt = new MemoryConstructor("MethodsAndConstructors(i : int)", DSVisibility.PRIVATE);
      addOperationObligations(constructorInt, true, false, true);
      methodsAndConstructors.addConstructor(constructorInt);
      MemoryConstructor constructorString = new MemoryConstructor("MethodsAndConstructors(j : java.lang.String)", DSVisibility.PROTECTED);
      addOperationObligations(constructorString, true, false, true);
      methodsAndConstructors.addConstructor(constructorString);
      MemoryConstructor constructorIntString = new MemoryConstructor("MethodsAndConstructors(i : int, j : java.lang.String)", DSVisibility.DEFAULT);
      addOperationObligations(constructorIntString, true, false, true);
      methodsAndConstructors.addConstructor(constructorIntString);
      MemoryMethod doSomething = new MemoryMethod("doSomething()", "void", DSVisibility.PUBLIC);
      addOperationObligations(doSomething, true, false, true);
      methodsAndConstructors.addMethod(doSomething);
      MemoryMethod doSomethingInt = new MemoryMethod("doSomething(i : int)", "int", DSVisibility.PUBLIC);
      addOperationObligations(doSomethingInt, true, false, true);
      methodsAndConstructors.addMethod(doSomethingInt);
      MemoryMethod doSomethingElse1 = new MemoryMethod("doSomethingElse(i : int[])", "java.lang.String", DSVisibility.PRIVATE);
      addOperationObligations(doSomethingElse1, true, false, true);
      methodsAndConstructors.addMethod(doSomethingElse1);
      MemoryMethod doSomethingElse2 = new MemoryMethod("doSomethingElse(i : int[][])", "java.lang.String", DSVisibility.PRIVATE);
      addOperationObligations(doSomethingElse2, true, false, true);
      methodsAndConstructors.addMethod(doSomethingElse2);
      MemoryMethod doSomethingArray = new MemoryMethod("doSomethingArray(sArray : java.lang.String[], myArray : MyClass[], boolArray : boolean[])", "java.lang.String[]", DSVisibility.PROTECTED);
      addOperationObligations(doSomethingArray, true, false, true);
      methodsAndConstructors.addMethod(doSomethingArray);
      MemoryMethod doSomethingElse3 = new MemoryMethod("doSomethingElse(i : int, c : MyClass)", "double", DSVisibility.DEFAULT);
      addOperationObligations(doSomethingElse3, true, false, true);
      methodsAndConstructors.addMethod(doSomethingElse3);
      MemoryMethod doStatic1 = new MemoryMethod("doStatic(i : int, c : MyClass)", "double", DSVisibility.DEFAULT, true);
      addOperationObligations(doStatic1, true, false, true);
      methodsAndConstructors.addMethod(doStatic1);
      MemoryMethod doStatic2 = new MemoryMethod("doStatic(x : java.lang.String)", "void", DSVisibility.PUBLIC, true, true);
      addOperationObligations(doStatic2, true, false, true);
      methodsAndConstructors.addMethod(doStatic2);
      MemoryMethod doAbstract = new MemoryMethod("doAbstract(x : java.lang.String)", "MyClass", DSVisibility.PROTECTED, false, false, true);
      addOperationObligations(doAbstract, true, false, true);
      methodsAndConstructors.addMethod(doAbstract);
      methodsAndConstructors.getExtendsFullnames().add("MethodsAndConstructorsParent");
      
      MemoryClass methodsAndConstructorsParent = new MemoryClass("MethodsAndConstructorsParent", DSVisibility.PUBLIC);
      methodsAndConstructors.getExtends().add(methodsAndConstructorsParent);
      con.addClass(methodsAndConstructorsParent);
      MemoryConstructor constructorParent = new MemoryConstructor("MethodsAndConstructorsParent()", DSVisibility.PUBLIC);
      addOperationObligations(constructorParent, true, false, true);
      methodsAndConstructorsParent.addConstructor(constructorParent);
      MemoryMethod staticParent = new MemoryMethod("staticParent()", "void", DSVisibility.PROTECTED, true);
      addOperationObligations(staticParent, true, false, true);
      methodsAndConstructorsParent.addMethod(staticParent);
      MemoryMethod doOnParent = new MemoryMethod("doOnParent(i : int)", "boolean", DSVisibility.PUBLIC);
      addOperationObligations(doOnParent, true, false, true);
      methodsAndConstructorsParent.addMethod(doOnParent);
      methodsAndConstructorsParent.getExtendsFullnames().add("java.lang.Object");
      
      MemoryClass myClass = new MemoryClass("MyClass", DSVisibility.PUBLIC);
      myClass.getExtendsFullnames().add("java.lang.Object");
      con.addClass(myClass);
      myClass.addConstructor(createDefaultConstructor("MyClass()", "X", false, false));
      return con;
   }

   /**
    * Creates the expected model for the accessible clause example with
    * {@link DSPackageManagement#FLAT_LIST}
    * @return The expected model.
    */   
   public static IDSConnection createExpectedAccessibleTestModel() {
      MemoryConnection con = new MemoryConnection();
      // Create package test
      MemoryPackage testPackage = new MemoryPackage("test");
      con.addPackage(testPackage);
      // Create class B
      MemoryClass b = new MemoryClass("B", DSVisibility.DEFAULT);
      b.getExtendsFullnames().add("java.lang.Object");
      b.addAttribute(new MemoryAttribute("c", "test.Test", bugAttributeVisibility(DSVisibility.PRIVATE), false, bugAttributeFinal(true)));
      b.addConstructor(new MemoryConstructor("B(x : int)", DSVisibility.DEFAULT));
      b.addInvariant(new MemoryInvariant("JML class invariant nr 0 in B", "self.c.<inv>"));
      MemoryAxiom axiom = new MemoryAxiom("Class invariant axiom for test.B", "equiv(java.lang.Object::<inv>(heap,self),java.lang.Object::<inv>(heap,test.Test::select(heap,self,test.B::$c)))");
      MemoryAxiomContract axiomContract = new MemoryAxiomContract("test.B[java.lang.Object::<inv>()].JML accessible clause.0", "self.<inv>", "allFields(self) \\cup allFields(self.c)");
      addAllOperationContractObligations(axiomContract);
      axiom.addAxiomContract(axiomContract);
      b.addAxiom(axiom);
      testPackage.addClass(b);
      // Create class test
      MemoryClass test = new MemoryClass("Test", DSVisibility.PUBLIC);
      test.getExtendsFullnames().add("java.lang.Object");
      test.addAttribute(new MemoryAttribute("x", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      test.addConstructor(new MemoryConstructor("Test(x : int)", DSVisibility.PUBLIC));
      testPackage.addClass(test);
      return con;
   }

   /**
    * Creates the expected model for the enumeration example with
    * {@link DSPackageManagement#FLAT_LIST}
    * @return The expected model.
    */     
   public static IDSConnection createExpectedEnumTestModel() {
      MemoryConnection con = new MemoryConnection();
      // Create package test
      MemoryPackage enumPackage = new MemoryPackage("enumPackage");
      con.addPackage(enumPackage);
      // Create interface IPackageEnum
      MemoryInterface iPackageEnum = new MemoryInterface("IPackageEnum", DSVisibility.PUBLIC);
      iPackageEnum.addMethod(new MemoryMethod("getValue()", "int", DSVisibility.PUBLIC, false, false, true));
      enumPackage.addInterface(iPackageEnum);
      // Create enumeration PackageEnum
      MemoryEnum packageEnum = new MemoryEnum("PackageEnum", bugEnumVisibility(DSVisibility.PUBLIC));
      packageEnum.getImplements().add(iPackageEnum);
      packageEnum.getImplementsFullnames().add("enumPackage.IPackageEnum");
      packageEnum.addLiteral(new MemoryEnumLiteral("RED"));
      packageEnum.addLiteral(new MemoryEnumLiteral("GREEN"));
      packageEnum.addLiteral(new MemoryEnumLiteral("BLUE"));
      packageEnum.addConstructor(createDefaultConstructor("PackageEnum()", null, false));
      packageEnum.addMethod(new MemoryMethod("getValue()", "int", DSVisibility.PUBLIC));
      packageEnum.addInvariant(new MemoryInvariant("JML class invariant nr 4 in PackageEnum", "!enumPackage.PackageEnum.RED = null"));
      packageEnum.addInvariant(new MemoryInvariant("JML class invariant nr 5 in PackageEnum", "!enumPackage.PackageEnum.GREEN = null"));
      packageEnum.addInvariant(new MemoryInvariant("JML class invariant nr 6 in PackageEnum", "!enumPackage.PackageEnum.BLUE = null"));
      enumPackage.addEnum(packageEnum);
      addDefaultEnumMethods(packageEnum, "enumPackage.PackageEnum");
      // Create enumeration MyEnum
      MemoryEnum myEnum = new MemoryEnum("MyEnum", bugEnumVisibility(DSVisibility.PUBLIC));
      myEnum.addLiteral(new MemoryEnumLiteral("A"));
      myEnum.addLiteral(new MemoryEnumLiteral("B"));
      myEnum.addLiteral(new MemoryEnumLiteral("C"));
      myEnum.addAttribute(new MemoryAttribute("previous", "MyEnum", bugAttributeVisibility(DSVisibility.PRIVATE)));
      myEnum.addConstructor(new MemoryConstructor("MyEnum(previous : MyEnum)", DSVisibility.PRIVATE));
      myEnum.addMethod(new MemoryMethod("getValue()", "int", DSVisibility.PUBLIC));
      myEnum.addMethod(new MemoryMethod("getPrevious()", "MyEnum", DSVisibility.PUBLIC));
      myEnum.addInvariant(new MemoryInvariant("JML class invariant nr 0 in MyEnum", "!MyEnum.A = null"));
      myEnum.addInvariant(new MemoryInvariant("JML class invariant nr 1 in MyEnum", "!MyEnum.B = null"));
      myEnum.addInvariant(new MemoryInvariant("JML class invariant nr 2 in MyEnum", "!MyEnum.C = null"));
      myEnum.addInvariant(new MemoryInvariant("JML class invariant nr 3 in MyEnum", "!self.previous = null"));
      addDefaultEnumMethods(myEnum, "MyEnum");
      con.addEnum(myEnum);
      return con;
   }

   /**
    * Adds the default methods that every enumeration has to the given {@link MemoryEnum}.
    * @param enumeration The {@link MemoryEnum} to fill.
    * @param fullName The full name of the enumeration.
    */
   protected static void addDefaultEnumMethods(MemoryEnum enumeration, String fullName) {
      enumeration.addMethod(new MemoryMethod("valueOf(string : java.lang.String)", fullName, DSVisibility.PUBLIC, true));
      enumeration.addMethod(new MemoryMethod("values()", fullName + "[]", DSVisibility.PUBLIC, true));
      enumeration.addMethod(new MemoryMethod("name()", "java.lang.String", DSVisibility.PUBLIC));
   }

   /**
    * Creates the expected model for the model field example with
    * {@link DSPackageManagement#FLAT_LIST}
    * @param includeAxiomContract {@code true} include, {@code false} do not include axiom contract
    * @return The expected model.
    */      
   public static IDSConnection createExpectedModelFieldTestModel(boolean includeAxiomContract) {
      MemoryConnection con = new MemoryConnection();
      MemoryClass b = new MemoryClass("ModelFieldTest", DSVisibility.PUBLIC);
      b.getExtendsFullnames().add("java.lang.Object");
      b.addAttribute(new MemoryAttribute("f", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      b.addAttribute(new MemoryAttribute("x", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      b.addConstructor(createDefaultConstructor("ModelFieldTest()", null, false));
      MemoryMethod doubleX = new MemoryMethod("doubleX()", "int", DSVisibility.PUBLIC);
      MemoryOperationContract doubleXcontract = new MemoryOperationContract(TestKeY4EclipseUtil.createOperationContractId("ModelFieldTest", "ModelFieldTest", "doubleX()", "0", null),
                                                                            "self.<inv>", 
                                                                            "(exc = null -> result = self.f & self.<inv>)\n& exc = null", 
                                                                            "mod[heap]: allLocs", 
                                                                            "diamond");
      addAllOperationContractObligations(doubleXcontract);
      doubleX.addOperationContract(doubleXcontract);
      b.addMethod(doubleX);
      MemoryAxiom axiom1 = new MemoryAxiom("JML represents clause for ModelFieldTest::$f", "equals(ModelFieldTest::$f(heap,self),javaMulInt(Z(2(#)),int::select(heap,self,ModelFieldTest::$x)))");
      if (includeAxiomContract) {
         MemoryAxiomContract axiom1contract = new MemoryAxiomContract(TestKeY4EclipseUtil.createAxiomContractId("ModelFieldTest", "$f()", "0"),
                                                                      "self.<inv>", 
                                                                      "{(self, x)}");
         addAllOperationContractObligations(axiom1contract);
         axiom1.addAxiomContract(axiom1contract);
      }
      b.addAxiom(axiom1);
      con.addClass(b);
      return con;
   }

   /**
    * Creates the expected model for the attributes example with
    * {@link DSPackageManagement#FLAT_LIST}
    * @return The expected model.
    */
   public static IDSConnection createExpectedAttributeTestModel() {
      MemoryConnection con = new MemoryConnection();
      MemoryClass attributeTestParent = new MemoryClass("AttributeTestParent", DSVisibility.PUBLIC);
      attributeTestParent.addConstructor(createDefaultConstructor("AttributeTestParent()", "X"));
      attributeTestParent.addAttribute(new MemoryAttribute("onParentMyClass", "MyClass", bugAttributeVisibility(DSVisibility.DEFAULT)));
      attributeTestParent.addAttribute(new MemoryAttribute("onParentBool", "boolean[][]", bugAttributeVisibility(DSVisibility.PRIVATE)));
      attributeTestParent.addAttribute(new MemoryAttribute("onParentInt", "int", bugAttributeVisibility(DSVisibility.PROTECTED)));
      attributeTestParent.addAttribute(new MemoryAttribute("onParentStringArray", "java.lang.String[]", bugAttributeVisibility(DSVisibility.PUBLIC)));
      attributeTestParent.addAttribute(new MemoryAttribute("PARENT_CONSTANT", "int", bugAttributeVisibility(DSVisibility.PUBLIC), true, bugAttributeFinal(true)));
      attributeTestParent.getExtendsFullnames().add("java.lang.Object");
      attributeTestParent.addInvariant(new MemoryInvariant("JML class invariant nr 0 in AttributeTestParent", "!self.onParentMyClass = null"));
      attributeTestParent.addInvariant(new MemoryInvariant("JML class invariant nr 1 in AttributeTestParent", "\\forall int i;\n" +
      		                                                                                                  "  (   0 <= i & i < self.onParentBool.length & inInt(i)\n" +
      		                                                                                                  "   -> !self.onParentBool[i] = null)"));
      attributeTestParent.addInvariant(new MemoryInvariant("JML class invariant nr 2 in AttributeTestParent", "!self.onParentBool = null"));
      attributeTestParent.addInvariant(new MemoryInvariant("JML class invariant nr 3 in AttributeTestParent", "\\forall int i;\n" +
      		                                                                                                  "  (     0 <= i\n" +
      		                                                                                                  "      & i < self.onParentStringArray.length\n" +
      		                                                                                                  "      & inInt(i)\n" +
      		                                                                                                  "   -> !self.onParentStringArray[i] = null)"));
      attributeTestParent.addInvariant(new MemoryInvariant("JML class invariant nr 4 in AttributeTestParent", "!self.onParentStringArray = null"));
      con.addClass(attributeTestParent);
      MemoryClass attributeTest = new MemoryClass("AttributesTest", DSVisibility.PUBLIC);
      attributeTest.addConstructor(createDefaultConstructor("AttributesTest()", "X"));
      attributeTest.addAttribute(new MemoryAttribute("x", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      attributeTest.addAttribute(new MemoryAttribute("y", "java.lang.String", bugAttributeVisibility(DSVisibility.DEFAULT)));
      attributeTest.addAttribute(new MemoryAttribute("boolArray", "boolean[]", bugAttributeVisibility(DSVisibility.PUBLIC)));
      attributeTest.addAttribute(new MemoryAttribute("classInstance", "MyClass", bugAttributeVisibility(DSVisibility.PROTECTED)));
      attributeTest.addAttribute(new MemoryAttribute("CONST", "java.lang.String", bugAttributeVisibility(DSVisibility.PRIVATE), false, bugAttributeFinal(true)));
      attributeTest.addAttribute(new MemoryAttribute("counter", "int", bugAttributeVisibility(DSVisibility.PRIVATE), true));
      attributeTest.getExtendsFullnames().add("AttributeTestParent");
      attributeTest.getExtends().add(attributeTestParent);
      attributeTest.addInvariant(new MemoryInvariant("JML class invariant nr 5 in AttributesTest", "!self.y = null"));
      attributeTest.addInvariant(new MemoryInvariant("JML class invariant nr 6 in AttributesTest", "!self.boolArray = null"));
      attributeTest.addInvariant(new MemoryInvariant("JML class invariant nr 7 in AttributesTest", "!self.classInstance = null"));
      attributeTest.addInvariant(new MemoryInvariant("JML class invariant nr 8 in AttributesTest", "!self.CONST = null"));
      attributeTest.addInvariant(new MemoryInvariant("JML class invariant nr 3 in AttributesTest", "\\forall int i;\n" +
                                                                                                        "  (     0 <= i\n" +
                                                                                                        "      & i < self.onParentStringArray.length\n" +
                                                                                                        "      & inInt(i)\n" +
                                                                                                        "   -> !self.onParentStringArray[i] = null)"));
      attributeTest.addInvariant(new MemoryInvariant("JML class invariant nr 4 in AttributesTest", "!self.onParentStringArray = null"));
      con.addClass(attributeTest);
      MemoryClass myClass = new MemoryClass("MyClass", DSVisibility.PUBLIC);
      myClass.getExtendsFullnames().add("java.lang.Object");
      con.addClass(myClass);
      myClass.addConstructor(createDefaultConstructor("MyClass()", "X", false, false));
      return con;
   }

   /**
    * Creates a default constructor.
    * @param name The name of the constructor.
    * @param operationContractId The operation contract ID to use.
    * @return The created default constructor.
    */
   public static MemoryConstructor createDefaultConstructor(String name, 
                                                            String operationContractId) {
      return createDefaultConstructor(name, operationContractId, false);
   }

   /**
    * Creates a default constructor.
    * @param name The name of the constructor.
    * @param operationContractId The operation contract ID to use.
    * @param addContract Defines if the default contract is added or not.
    * @return The created default constructor.
    */
   public static MemoryConstructor createDefaultConstructor(String name, 
                                                            String operationContractId, 
                                                            boolean addContract) {
      return createDefaultConstructor(name, operationContractId, addContract, true);
   }

   /**
    * Creates a default constructor.
    * @param name The name of the constructor.
    * @param operationContractId The operation contract ID to use.
    * @param addContract Defines if the default contract is added or not.
    * @param addPreservesOwnInv Add preserves own inv?
    * @return The created default constructor.
    */
   public static MemoryConstructor createDefaultConstructor(String name, 
                                                            String operationContractId, 
                                                            boolean addContract, 
                                                            boolean addPreservesOwnInv) {
      MemoryConstructor result = new MemoryConstructor(name, DSVisibility.DEFAULT); // Default constructor is always added
      if (addContract) {
         MemoryOperationContract contract = new MemoryOperationContract("JML normal_behavior operation contract (id: " + operationContractId + ")", "true", "exc = null", "{}", "diamond");
         addAllOperationContractObligations(contract);
         result.addOperationContract(contract);
      }
      addOperationObligations(result, true, addPreservesOwnInv, true);
      return result;
   }

   /**
    * Creates the expected model for the type invariant example with
    * {@link DSPackageManagement#FLAT_LIST}
    * @return The expected model.
    */   
   public static IDSConnection createExpectedTypeInvariantTestModel() {
      MemoryConnection con = new MemoryConnection();
      MemoryClass classA = new MemoryClass("ClassA", DSVisibility.PUBLIC);
      classA.addConstructor(createDefaultConstructor("ClassA()", "X"));
      classA.addAttribute(new MemoryAttribute("limit", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      classA.getExtendsFullnames().add("java.lang.Object");
      classA.addInvariant(new MemoryInvariant("JML class invariant nr 0 in ClassA", "self.limit >  0"));
      con.addClass(classA);
      MemoryInterface interfaceA = new MemoryInterface("InterfaceA", DSVisibility.PUBLIC);
      MemoryMethod getLimit = new MemoryMethod("getLimit()", "int", DSVisibility.PUBLIC, false, false, true);
      addOperationObligations(getLimit, true, true, true);
      interfaceA.addMethod(getLimit);
      interfaceA.addInvariant(new MemoryInvariant("JML class invariant nr 2 in InterfaceA", "self.getLimit() >  0"));
      con.addInterface(interfaceA);
      return con;
   }

   /**
    * Creates the expected model for the operation contract example with
    * {@link DSPackageManagement#FLAT_LIST}
    * @return The expected model.
    */     
   public static IDSConnection createExpectedOperationContractTestModel() {
      MemoryConnection con = new MemoryConnection();
      MemoryClass classA = new MemoryClass("ClassA", DSVisibility.PUBLIC);
      MemoryConstructor classAConstructor = new MemoryConstructor("ClassA()", DSVisibility.PUBLIC);
      addOperationObligations(classAConstructor, true, false, true);
      MemoryOperationContract oc12 = new MemoryOperationContract("JML normal_behavior operation contract (id: 12)", "true", "exc = null", "{}", "diamond");
      addAllOperationContractObligations(oc12);
      MemoryOperationContract oc4 = new MemoryOperationContract("JML normal_behavior operation contract (id: 4)", "self.x = 0", "self.x = (jint)(5) & exc = null", "{}", "diamond");
      addAllOperationContractObligations(oc4);
      MemoryOperationContract oc0 = new MemoryOperationContract("JML normal_behavior operation contract (id: 0)", "true", "self.x = (jint)(5) & exc = null", "{}", "diamond");
      addAllOperationContractObligations(oc0);
      classAConstructor.addOperationContract(oc12);
      classAConstructor.addOperationContract(oc4);
      classAConstructor.addOperationContract(oc0);
      classA.addConstructor(classAConstructor);
      MemoryConstructor classAConstructorInt = new MemoryConstructor("ClassA(x : int)", DSVisibility.PUBLIC);
      addOperationObligations(classAConstructorInt, true, false, true);
      MemoryOperationContract oc5 = new MemoryOperationContract("JML normal_behavior operation contract (id: 5)", "self.x = 0", "self.x = x & exc = null", "{}", "diamond");
      addAllOperationContractObligations(oc5);
      MemoryOperationContract oc1 = new MemoryOperationContract("JML normal_behavior operation contract (id: 1)", "true", "self.x = x & exc = null", "{}", "diamond");
      addAllOperationContractObligations(oc1);
      classAConstructorInt.addOperationContract(oc5);
      classAConstructorInt.addOperationContract(oc1);
      classA.addConstructor(classAConstructorInt);
      classA.addAttribute(new MemoryAttribute("x", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      classA.getExtendsFullnames().add("java.lang.Object");
      MemoryMethod classAGetX = new MemoryMethod("getX()", "int", DSVisibility.PUBLIC);
      addOperationObligations(classAGetX, true, false, true);
      MemoryOperationContract oc2 = new MemoryOperationContract("JML normal_behavior operation contract (id: 2)", "true", "result = self.x & exc = null", "{}", "diamond");
      addAllOperationContractObligations(oc2);
      classAGetX.addOperationContract(oc2);
      classA.addMethod(classAGetX);
      MemoryMethod classASetX = new MemoryMethod("setX(x : int)", "void", DSVisibility.PUBLIC);
      addOperationObligations(classASetX, true, false, true);
      MemoryOperationContract oc3 = new MemoryOperationContract("JML normal_behavior operation contract (id: 3)", "true", "self.x = x & exc = null", "{}", "diamond");
      addAllOperationContractObligations(oc3);
      classASetX.addOperationContract(oc3);
      classA.addMethod(classASetX);
      con.addClass(classA);
      MemoryMethod interfaceAGetX = new MemoryMethod("getX()", "int", DSVisibility.PUBLIC, false, false, true);
      addOperationObligations(interfaceAGetX, true, false, true);
      MemoryOperationContract oc6 = new MemoryOperationContract("JML normal_behavior operation contract (id: 6)", "true", "exc = null", "{}", "diamond");
      addAllOperationContractObligations(oc6);
      interfaceAGetX.addOperationContract(oc6);
      MemoryInterface interfaceA = new MemoryInterface("InterfaceA", DSVisibility.PUBLIC);
      interfaceA.addMethod(interfaceAGetX);
      con.addInterface(interfaceA);
      return con;
   }

   /**
    * Creates the expected model for the constructor example with
    * {@link DSPackageManagement#FLAT_LIST}
    * @return The expected model.
    */
   public static IDSConnection createExpectedConstructorTestModel() {
      MemoryConnection con = new MemoryConnection();
      MemoryClass classA = new MemoryClass("A", DSVisibility.PUBLIC);
      classA.getExtendsFullnames().add("java.lang.Object");
      MemoryMethod classAmagic = new MemoryMethod("magic()", "int", DSVisibility.PUBLIC);
      MemoryMethod classAstaticMagic = new MemoryMethod("staticMagic()", "int", DSVisibility.PUBLIC, true);
      classA.addMethod(classAmagic);
      classA.addMethod(classAstaticMagic);
      classA.addConstructor(createDefaultConstructor("A()", null, false));
      MemoryClass classB = new MemoryClass("B", DSVisibility.PUBLIC);
      classB.getExtendsFullnames().add("A");
      classB.getExtends().add(classA);
      MemoryMethod classBstaticMagic = new MemoryMethod("staticMagic()", "int", DSVisibility.PUBLIC, true);
      classB.addMethod(classBstaticMagic);
      classB.addConstructor(createDefaultConstructor("B()", null, false));
      MemoryClass classConstructor = new MemoryClass("ConstructorTest", DSVisibility.PUBLIC);
      classConstructor.getExtendsFullnames().add("java.lang.Object");
      classConstructor.addAttribute(new MemoryAttribute("value", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      MemoryConstructor classConstructorConstructor = new MemoryConstructor("ConstructorTest(x : int, a : B)", DSVisibility.PUBLIC);
      classConstructor.addConstructor(classConstructorConstructor);
      MemoryOperationContract classConstructorConstructorOC = new MemoryOperationContract("ConstructorTest[ConstructorTest::ConstructorTest(int,B)].JML operation contract.0", "!a = null", "(   exc = null\n   -> self.value = javaSubInt(42, 4711) & self.<inv>)\n& exc = null", "mod[heap]: allLocs", "diamond");
      addAllOperationContractObligations(classConstructorConstructorOC);
      classConstructorConstructor.addOperationContract(classConstructorConstructorOC);
      con.addClass(classA);
      con.addClass(classB);
      con.addClass(classConstructor);
      return con;
   }
   
   /**
    * Creates the expected model for the generalization example with
    * {@link DSPackageManagement#FLAT_LIST}
    * @return The expected model.
    */   
   public static IDSConnection createExpectedGeneralizationTestModel() {
      MemoryConnection con = new MemoryConnection();
      // package A
      MemoryPackage packageA = new MemoryPackage("a");
      con.addPackage(packageA);
      MemoryClass classInA = new MemoryClass("ClassInA", DSVisibility.PUBLIC);
      classInA.addConstructor(createDefaultConstructor("ClassInA()", "X", false, false));
      classInA.getExtendsFullnames().add("java.lang.Object");
      packageA.addClass(classInA);
      MemoryInterface interfaceInA = new MemoryInterface("InterfaceInA", DSVisibility.PUBLIC);
      packageA.addInterface(interfaceInA);
      // package B
      MemoryPackage packageB = new MemoryPackage("b");
      con.addPackage(packageB);
      MemoryClass classInB = new MemoryClass("ClassInB", DSVisibility.PUBLIC);
      classInB.addConstructor(createDefaultConstructor("ClassInB()", "X", false, false));
      classInB.getExtendsFullnames().add("a.ClassInA");
      classInB.getExtends().add(classInA);
      classInB.getImplementsFullnames().add("a.InterfaceInA");
      classInB.getImplements().add(interfaceInA);
      packageB.addClass(classInB);
      MemoryInterface interfaceInB = new MemoryInterface("InterfaceInB", DSVisibility.PUBLIC);
      interfaceInB.getExtendsFullnames().add("a.InterfaceInA");
      interfaceInB.getExtends().add(interfaceInA);
      packageB.addInterface(interfaceInB);
      // Default package (interfaces)
      MemoryInterface interfaceB = new MemoryInterface("InterfaceB", DSVisibility.PUBLIC);
      con.addInterface(interfaceB);
      MemoryInterface interfaceC = new MemoryInterface("InterfaceC", DSVisibility.PUBLIC);
      interfaceC.getExtendsFullnames().add("InterfaceB");
      interfaceC.getExtends().add(interfaceB);
      con.addInterface(interfaceC);
      MemoryInterface interfaceX = new MemoryInterface("InterfaceX", DSVisibility.PUBLIC);
      con.addInterface(interfaceX);
      MemoryInterface packageInterface = new MemoryInterface("PackageInterface", DSVisibility.PUBLIC);
      packageInterface.getExtendsFullnames().add("a.InterfaceInA");
      packageInterface.getExtends().add(interfaceInA);
      packageInterface.getExtendsFullnames().add("InterfaceB");
      packageInterface.getExtends().add(interfaceB);
      con.addInterface(packageInterface);
      // Default package (classes)
      MemoryClass a = new MemoryClass("A", DSVisibility.PUBLIC);
      a.addConstructor(createDefaultConstructor("A()", "X", false, false));
      a.getExtendsFullnames().add("java.lang.Object");
      con.addClass(a);
      MemoryClass b = new MemoryClass("B", DSVisibility.PUBLIC);
      b.addConstructor(createDefaultConstructor("B()", "X", false, false));
      b.getExtendsFullnames().add("A");
      b.getExtends().add(a);
      b.getImplementsFullnames().add("InterfaceB");
      b.getImplements().add(interfaceB);
      con.addClass(b);
      MemoryClass c = new MemoryClass("CX", DSVisibility.PUBLIC);
      c.addConstructor(createDefaultConstructor("CX()", "X", false, false));
      c.getExtendsFullnames().add("B");
      c.getExtends().add(b);
      c.getImplementsFullnames().add("InterfaceC");
      c.getImplements().add(interfaceC);
      c.getImplementsFullnames().add("InterfaceX");
      c.getImplements().add(interfaceX);
      con.addClass(c);
      MemoryClass packageClass = new MemoryClass("PackageClass", DSVisibility.PUBLIC);
      packageClass.addConstructor(createDefaultConstructor("PackageClass()", "X", false, false));
      packageClass.getExtendsFullnames().add("b.ClassInB");
      packageClass.getExtends().add(classInB);
      packageClass.getImplementsFullnames().add("a.InterfaceInA");
      packageClass.getImplements().add(interfaceInA);
      con.addClass(packageClass);
      MemoryClass x = new MemoryClass("X", DSVisibility.PUBLIC);
      x.addConstructor(createDefaultConstructor("X()", "X", false, false));
      x.getExtendsFullnames().add("java.lang.Object");
      x.getImplementsFullnames().add("InterfaceX");
      x.getImplements().add(interfaceX);
      con.addClass(x);      
      return con;
   }
   /**
    * Creates the expected model for the type flags example with
    * {@link DSPackageManagement#FLAT_LIST}
    * @return The expected model.
    */   
   public static IDSConnection createExpectedTypeTestModel() {
      MemoryConnection con = new MemoryConnection();
      MemoryClass myAbstractClass = new MemoryClass("MyAbstractClass", DSVisibility.PUBLIC, true);
      myAbstractClass.addConstructor(createDefaultConstructor("MyAbstractClass()", "X", false, false));
      myAbstractClass.getExtendsFullnames().add("java.lang.Object");
      con.addClass(myAbstractClass);
      MemoryClass myDefaultClass = new MemoryClass("MyDefaultClass", DSVisibility.DEFAULT);
      myDefaultClass.addConstructor(createDefaultConstructor("MyDefaultClass()", "X", false, false));
      myDefaultClass.getExtendsFullnames().add("java.lang.Object");
      con.addClass(myDefaultClass);
      MemoryInterface myDefaultInterface = new MemoryInterface("MyDefaultInterface", DSVisibility.DEFAULT);
      con.addInterface(myDefaultInterface);
      MemoryClass myFinalClass = new MemoryClass("MyFinalClass", DSVisibility.PUBLIC, false, true);
      myFinalClass.addConstructor(createDefaultConstructor("MyFinalClass()", "X", false, false));
      myFinalClass.getExtendsFullnames().add("java.lang.Object");
      con.addClass(myFinalClass);
      MemoryClass myPublicClass = new MemoryClass("MyPublicClass", DSVisibility.PUBLIC);
      myPublicClass.addConstructor(createDefaultConstructor("MyPublicClass()", "X", false, false));
      myPublicClass.getExtendsFullnames().add("java.lang.Object");
      con.addClass(myPublicClass);
      MemoryInterface myPublicInterface = new MemoryInterface("MyPublicInterface", DSVisibility.PUBLIC);
      con.addInterface(myPublicInterface);
      return con;
   }

   /**
    * Creates the expected model for the inner type example with  
    * {@link DSPackageManagement#FLAT_LIST}
    * @return The expected model.
    */   
   public static IDSConnection createExpectedInnerTypeTestModel() {
      MemoryConnection con = new MemoryConnection();
      MemoryPackage interfaces = new MemoryPackage("interfaces");
      con.addPackage(interfaces);      
      MemoryInterface myInterface = new MemoryInterface("MyInterface", DSVisibility.PUBLIC);
      interfaces.addInterface(myInterface);

      MemoryPackage packageC = new MemoryPackage("packageA.B.C");
      con.addPackage(packageC);
      packageC.addClass(createClassContainer("ClassContainer", packageC.getName(), new String[] {"6", "7", "8"}, true));
      packageC.addEnum(createEnumContainer("EnumContainer", packageC.getName(), new String[] {"9"}, true));
      packageC.addInterface(createInterfaceContainer("InterfaceContainer", packageC.getName(), new String[] {"10", "11"}, true));

      MemoryPackage packageB = new MemoryPackage("packageA.B");
      con.addPackage(packageB);
      packageB.addClass(createClassContainer("ClassContainer", packageB.getName(), new String[] {"12", "13", "14"}, true));
      packageB.addEnum(createEnumContainer("EnumContainer", packageB.getName(), new String[] {"15"}, true));
      packageB.addInterface(createInterfaceContainer("InterfaceContainer", packageB.getName(), new String[] {"16", "17"}, true));
      
      MemoryPackage packageA = new MemoryPackage("packageA");
      con.addPackage(packageA);
      packageA.addClass(createClassContainer("ClassContainer", packageA.getName(), new String[] {"18", "19", "20"}, true));
      packageA.addEnum(createEnumContainer("EnumContainer", packageA.getName(), new String[] {"21"}, true));
      packageA.addInterface(createInterfaceContainer("InterfaceContainer", packageA.getName(), new String[] {"22", "23"}, true));
      
      con.addClass(createClassContainer("ClassContainer", null, new String[] {"0", "1", "2"}, false));
      con.addEnum(createEnumContainer("EnumContainer", null, new String[] {"3"}, false));
      con.addInterface(createInterfaceContainer("InterfaceContainer", null, new String[] {"4", "5"}, false));
      return con;
   }
   
   /**
    * Creates the class "ClassContainer".
    * @param className The name to use.
    * @param packageName The package name to use.
    * @param enumInvariantIds The invariant IDs to use.
    * @param multilineInvariant Are invariants multilined?
    * @return The created {@link IDSClass}.
    */
   protected static MemoryClass createClassContainer(String className, String packageName, String[] enumInvariantIds, boolean multilineInvariant) {
      MemoryClass result = new MemoryClass(className, DSVisibility.PUBLIC);
      result.addConstructor(createDefaultConstructor(className + "()", "X", false, false));
      MemoryClass anonymousClass = new MemoryClass("ClassContainer.30390029.20920809", DSVisibility.DEFAULT);
      anonymousClass.setAnonymous(true);
      anonymousClass.getExtendsFullnames().add("java.lang.Object");
      result.addInnerClass(anonymousClass);
      result.addInnerClass(createDefaultChildClass());
      result.addInnerClass(createPrivateChildClass());
      result.addInnerClass(createProtectedChildClass());
      result.addInnerClass(createPublicChildClass());
      result.addInnerInterface(createDefaultChildInterface());
      result.addInnerInterface(createPrivateChildInterface());
      result.addInnerInterface(createProtectedChildInterface());
      result.addInnerInterface(createPublicChildInterface());
      MemoryMethod doContainer = new MemoryMethod("doContainer()", "void", DSVisibility.PUBLIC);
      addOperationObligations(doContainer, true, false, true);
      result.addMethod(doContainer);
      result.getExtendsFullnames().add("java.lang.Object");
      result.addInnerEnum(createDefaultChildEnum("DefaultChildEnum", (!StringUtil.isEmpty(packageName) ? packageName + "." : StringUtil.EMPTY_STRING) + "ClassContainer", enumInvariantIds[0], multilineInvariant));
      result.addInnerEnum(createPrivateChildEnum("PrivateChildEnum", (!StringUtil.isEmpty(packageName) ? packageName + "." : StringUtil.EMPTY_STRING) + "ClassContainer", enumInvariantIds[1], multilineInvariant));
      result.addInnerEnum(createProtectedChildEnum("ProtectedChildEnum", (!StringUtil.isEmpty(packageName) ? packageName + "." : StringUtil.EMPTY_STRING) + "ClassContainer"));
      result.addInnerEnum(createPublicChildEnum("PublicChildEnum", (!StringUtil.isEmpty(packageName) ? packageName + "." : StringUtil.EMPTY_STRING) + "ClassContainer", enumInvariantIds[2], multilineInvariant));
      return result;
   }
   
   /**
    * Creates the class "ClassContainer".
    * @param className The name to use.
    * @param packageName The package name to use.
    * @param enumInvariantIds The invariant IDs to use.
    * @param multilineInvariant Are invariants multilined?
    * @return The created {@link IDSClass}.
    */
   protected static MemoryEnum createEnumContainer(String className, String packageName, String[] enumInvariantIds, boolean multilineInvariant) {
      String fullName = (packageName != null ? packageName + "." : "") + className;
      MemoryEnum result = new MemoryEnum(className, bugEnumVisibility(DSVisibility.PUBLIC));
      result.addConstructor(createDefaultConstructor(className + "()", null, false));
      result.addLiteral(new MemoryEnumLiteral("INSTANCE"));
//      if (multilineInvariant) {
//         result.addInvariant(new MemoryInvariant("JML class invariant nr " + enumInvariantIds[0] + " in " + className, "!  " + fullName + ".INSTANCE\n = null"));
//      }
//      else {
         result.addInvariant(new MemoryInvariant("JML class invariant nr " + enumInvariantIds[0] + " in " + className, "!" + fullName + ".INSTANCE = null"));
//      }
      MemoryClass anonymousClass = new MemoryClass("ClassContainer.30390029.20920809", DSVisibility.DEFAULT);
      anonymousClass.setAnonymous(true);
      anonymousClass.getExtendsFullnames().add("java.lang.Object");
      result.addInnerClass(anonymousClass);
      result.addInnerClass(createDefaultChildClass());
      result.addInnerClass(createPrivateChildClass());
      result.addInnerClass(createProtectedChildClass());
      result.addInnerClass(createPublicChildClass());
      result.addInnerInterface(createDefaultChildInterface());
      result.addInnerInterface(createPrivateChildInterface());
      result.addInnerInterface(createProtectedChildInterface());
      result.addInnerInterface(createPublicChildInterface());
      MemoryMethod doContainer = new MemoryMethod("doContainer()", "void", DSVisibility.PUBLIC);
      addOperationObligations(doContainer, true, false, true);
      result.addMethod(doContainer);
      addDefaultEnumMethods(result, fullName);
      return result;
   }
   
   /**
    * Creates the enumeration "PublicChildEnum".
    * @param className The class name to use.
    * @param packageName The package in that the class is contained.
    * @param invariantId The invariant ID to use.
    * @param multilineInvariant Is invariant multilined?
    * @return The created {@link IDSEnum}.
    */
   protected static MemoryEnum createPublicChildEnum(String className, String packageName, String invariantId, boolean multilineInvariant) {
      String fullName = (packageName != null ? packageName + "." : "") + className;
      MemoryEnum result = new MemoryEnum(className, bugEnumVisibility(DSVisibility.DEFAULT));
      result.addConstructor(createDefaultConstructor(className + "()", null, false));
      result.addLiteral(new MemoryEnumLiteral("INSTANCE"));
      if (multilineInvariant) {
         result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantId + " in " + className, "!  " + fullName + ".INSTANCE\n = null"));
      }
      else {
         result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantId + " in " + className, "!" + fullName + ".INSTANCE = null"));
      }
      addDefaultEnumMethods(result, fullName);
      return result;
   }

   /**
    * Creates the enumeration "ProtectedChildEnum".
    * @param className The class name to use.
    * @param packageName The package in that the class is contained.
    * @param invariantId The invariant ID to use.
    * @param multilineInvariant Is invariant multilined?
    * @return The created {@link IDSEnum}.
    */
   protected static MemoryEnum createProtectedChildEnum(String className, String packageName) {
      String fullName = (packageName != null ? packageName + "." : "") + className;
      MemoryEnum result = new MemoryEnum(className, bugEnumVisibility(DSVisibility.DEFAULT));
      result.addConstructor(createDefaultConstructor(className + "()", null, false));
      addDefaultEnumMethods(result, fullName);
      return result;
   }

   /**
    * Creates the enumeration "PrivateChildEnum".
    * @param className The class name to use.
    * @param packageName The package in that the class is contained.
    * @param invariantId The invariant ID to use.
    * @param multilineInvariant Is invariant multilined?
    * @return The created {@link IDSEnum}.
    */
   protected static MemoryEnum createPrivateChildEnum(String className, String packageName, String invariantId, boolean multilineInvariant) {
      String fullName = (packageName != null ? packageName + "." : "") + className;
      MemoryEnum result = new MemoryEnum(className, bugEnumVisibility(DSVisibility.DEFAULT));
      result.addConstructor(createDefaultConstructor(className + "()", null, false));
      result.addLiteral(new MemoryEnumLiteral("INSTANCE"));
      if (multilineInvariant) {
         result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantId + " in " + className, "!  " + fullName + ".INSTANCE\n = null"));
      }
      else {
         result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantId + " in " + className, "!" + fullName + ".INSTANCE = null"));
      }
      addDefaultEnumMethods(result, fullName);
      return result;
   }

   /**
    * Creates the enumeration "DefaultChildEnum".
    * @param className The class name to use.
    * @param packageName The package in that the class is contained.
    * @param invariantId The invariant ID to use.
    * @param multilineInvariant Is invariant multilined?
    * @return The created {@link IDSEnum}.
    */
   protected static MemoryEnum createDefaultChildEnum(String className, String packageName, String invariantId, boolean multilineInvariant) {
      String fullName = (!StringUtil.isEmpty(packageName) ? packageName + "." : StringUtil.EMPTY_STRING) + className;
      MemoryEnum result = new MemoryEnum(className, bugEnumVisibility(DSVisibility.DEFAULT));
      MemoryClass anonymousClass = new MemoryClass("ClassContainer.30390029.20920809", DSVisibility.DEFAULT);
      anonymousClass.setAnonymous(true);
      anonymousClass.getExtendsFullnames().add("java.lang.Object");
      result.addInnerClass(anonymousClass);
      result.addLiteral(new MemoryEnumLiteral("INSTANCE"));
      if (multilineInvariant) {
         result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantId + " in " + className, "!  " + fullName + ".INSTANCE\n = null"));
      }
      else {
         result.addInvariant(new MemoryInvariant("JML class invariant nr " + invariantId + " in " + className, "!" + fullName + ".INSTANCE = null"));
      }
      result.addAttribute(new MemoryAttribute("x", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      result.addConstructor(new MemoryConstructor(className + "(x : int)", DSVisibility.PRIVATE));
      MemoryMethod run = new MemoryMethod("run()", "void", DSVisibility.PUBLIC);
      addOperationObligations(run, true, false, true);
      result.addMethod(run);
      addDefaultEnumMethods(result, fullName);
      return result;
   }

   /**
    * Creates the interface "InterfaceContainer".
    * @param interfaceName The name to use.
    * @param packageName The package name to use.
    * @param enumInvariantIds The invariant IDs to use.
    * @param multilineInvariant Are invariants multilined?
    * @return The created {@link IDSInterface}.
    */
   protected static MemoryInterface createInterfaceContainer(String interfaceName, String packageName, String[] enumInvariantIds, boolean multilineInvariant) {
      MemoryInterface interfaceContainer = new MemoryInterface(interfaceName, DSVisibility.PUBLIC);
      interfaceContainer.addInnerClass(createDefaultChildClass());
      interfaceContainer.addInnerClass(createPublicChildClass());
      interfaceContainer.addInnerInterface(createDefaultChildInterface());
      interfaceContainer.addInnerInterface(createPublicChildInterface());
      interfaceContainer.addInnerEnum(createDefaultChildEnum("DefaultChildEnum", (!StringUtil.isEmpty(packageName) ? packageName + "." : StringUtil.EMPTY_STRING) + "InterfaceContainer", enumInvariantIds[0], multilineInvariant));
      interfaceContainer.addInnerEnum(createPublicChildEnum("PublicChildEnum", (!StringUtil.isEmpty(packageName) ? packageName + "." : StringUtil.EMPTY_STRING) + "InterfaceContainer", enumInvariantIds[1], multilineInvariant));
      return interfaceContainer;
   }
   
   /**
    * Creates the class "PrivateChildClass".
    * @return The created {@link IDSClass}.
    */   
   protected static MemoryClass createPrivateChildClass() {
      MemoryClass result = new MemoryClass("PrivateChildClass", DSVisibility.PRIVATE);
      result.setStatic(true);
      result.addConstructor(createDefaultConstructor("PrivateChildClass()", "X", false, false));
      result.addInnerInterface(createInnerInnerInterface());
      result.getExtendsFullnames().add("java.lang.Object");
      return result;
   }
   
   /**
    * Creates the interface "InnerInnerInterface".
    * @return The created {@link IDSInterface}.
    */      
   protected static MemoryInterface createInnerInnerInterface() {
      return new MemoryInterface("InnerInnerInterface", bugInnerInterfaceVisibility(DSVisibility.PUBLIC));
   }
   
   /**
    * Creates the class "DefaultChildClass".
    * @return The created {@link IDSClass}.
    */   
   protected static MemoryClass createDefaultChildClass() {
      MemoryClass result = new MemoryClass("DefaultChildClass", DSVisibility.DEFAULT);
      MemoryClass anonymousClass = new MemoryClass("ClassContainer.30390029.20920809", DSVisibility.DEFAULT);
      anonymousClass.setAnonymous(true);
      anonymousClass.getExtendsFullnames().add("java.lang.Object");
      result.addInnerClass(anonymousClass);
      result.addAttribute(new MemoryAttribute("x", "int", bugAttributeVisibility(DSVisibility.PRIVATE)));
      MemoryConstructor constructor = new MemoryConstructor("DefaultChildClass(x : int)", DSVisibility.PUBLIC);
      addOperationObligations(constructor, true, false, true);
      result.addConstructor(constructor);
      MemoryMethod run = new MemoryMethod("run()", "void", DSVisibility.PUBLIC);
      addOperationObligations(run, true, false, true);
      result.addMethod(run);
      result.getExtendsFullnames().add("java.lang.Object");
      return result;
   }
   
   /**
    * Creates the class "ProtectedChildClass".
    * @return The created {@link IDSClass}.
    */   
   protected static MemoryClass createProtectedChildClass() {
      MemoryClass result = new MemoryClass("ProtectedChildClass", DSVisibility.PROTECTED, true);
      result.addConstructor(createDefaultConstructor("ProtectedChildClass()", "X", false, false));
      result.getExtendsFullnames().add("java.lang.Object");
      return result;
   }
   
   /**
    * Creates the class "PublicChildClass".
    * @return The created {@link IDSClass}.
    */   
   protected static MemoryClass createPublicChildClass() {
      MemoryClass result = new MemoryClass("PublicChildClass", DSVisibility.PUBLIC, false, true);
      result.addConstructor(createDefaultConstructor("PublicChildClass()", "X", false, false));
      result.addInnerClass(createInnerInnerClass());
      result.getExtendsFullnames().add("java.lang.Object");
      return result;
   }
   
   /**
    * Creates the class "InnerInnerClass".
    * @return The created {@link IDSClass}.
    */     
   protected static MemoryClass createInnerInnerClass() {
      MemoryClass result = new MemoryClass("InnerInnerClass", DSVisibility.PUBLIC);
      MemoryClass anonymousClass = new MemoryClass("ClassContainer.30390029.20920809", DSVisibility.DEFAULT);
      anonymousClass.setAnonymous(true);
      anonymousClass.getExtendsFullnames().add("java.lang.Object");
      result.addInnerClass(anonymousClass);
      result.addConstructor(createDefaultConstructor("InnerInnerClass()", "X", false, false));
      MemoryMethod innerInnerRun = new MemoryMethod("innerInnerRun()", "void", DSVisibility.PUBLIC);
      addOperationObligations(innerInnerRun, true, false, true);  
      result.addMethod(innerInnerRun);
      result.getExtendsFullnames().add("java.lang.Object");
      return result;
   }
   
   /**
    * Creates the interface "PrivateChildInterface".
    * @return The created {@link IDSInterface}.
    */   
   protected static MemoryInterface createPrivateChildInterface() {
      MemoryInterface result = new MemoryInterface("PrivateChildInterface", bugInnerInterfaceVisibility(DSVisibility.PRIVATE));
      result.setStatic(true);
      return result;
   }
   
   /**
    * Creates the interface "DefaultChildInterface".
    * @return The created {@link IDSInterface}.
    */   
   protected static MemoryInterface createDefaultChildInterface() {
      MemoryInterface result = new MemoryInterface("DefaultChildInterface", bugInnerInterfaceVisibility(DSVisibility.DEFAULT));
      result.addInnerClass(createInnerInnerClass());
      result.addInnerInterface(createInnerInnerInterface());
      return result;
   }
   
   /**
    * Creates the interface "ProtectedChildInterface".
    * @return The created {@link IDSInterface}.
    */   
   protected static MemoryInterface createProtectedChildInterface() {
      return new MemoryInterface("ProtectedChildInterface", bugInnerInterfaceVisibility(DSVisibility.PROTECTED));
   }
   
   /**
    * Creates the interface "PublicChildInterface".
    * @return The created {@link IDSInterface}.
    */   
   protected static MemoryInterface createPublicChildInterface() {
      return new MemoryInterface("PublicChildInterface", bugInnerInterfaceVisibility(DSVisibility.PUBLIC));
   }

   /**
    * Executes a KeY connection test by extracting the test data in the 
    * new created project. After that the connection is opened to the
    * startContainerPath and compared with the expected connection.
    * Also a diagram is created from the opened key connection 
    * and compared with the expected connection.
    * @param projectName The name of the project to create.
    * @param testDataInBundle The path in the bundle to the test data.
    * @param startContainerPath The path to the container to connect to.
    * @param packageManagement The package management to use in the KeY connection
    * @param expectedConnection The expected information to compare to.
    * @throws Exception Occurred Exception.
    */
   public static void testKeyConnection(String projectName,
                                        String testDataInBundle,
                                        String startContainerPath,
                                        DSPackageManagement packageManagement,
                                        IDSConnection expectedConnection) throws Exception {
      IDSConnection connection = null;
      ConnectionLogger logger = new ConnectionLogger();
      try {
         // Create project and fill it with test data
         IProject project = TestUtilsUtil.createProject(projectName);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, testDataInBundle, project);
         IContainer paycardFolder;
         if (startContainerPath != null) {
            paycardFolder = project.getFolder(startContainerPath);
         }
         else {
            paycardFolder = project;
         }
         TestCase.assertNotNull(paycardFolder);
         TestCase.assertTrue(paycardFolder.exists());
         // Open connection
         File location = ResourceUtil.getLocation(paycardFolder); 
         TestCase.assertNotNull(location);
         TestCase.assertTrue(location.exists() && location.isDirectory());
         connection = createKeyConnection(location, packageManagement, logger);
         TestCase.assertTrue(connection.isConnected());
         TestDataSourceUtil.compareConnectionEvents(connection, logger, true, false, false);
         // Create diagram files
         IFile modelFile = paycardFolder.getFile(new Path("default.proof"));
         IFile diagramFile = paycardFolder.getFile(new Path("default.proof_diagram"));
         // Compare connection with expected one and created diagram
         compareModels(expectedConnection, connection, modelFile, diagramFile);
      }
      finally {
         try {
            if (connection != null) {
               TestGenerationUtil.closeConnection(connection);
               TestDataSourceUtil.compareConnectionEvents(connection, logger, false, false, true);
               if (connection != null) {
                  connection.removeConnectionListener(logger);
                  TestCase.assertEquals(0, connection.getConnectionListeners().length);
               }
               TestGenerationUtil.closeConnection(expectedConnection);
            }
         }
         catch (DSException e) {
            e.printStackTrace();
            fail(e.getMessage());
         }
      }
   }
   
   /**
    * Compares the given {@link IDSConnection} with the expected
    * {@link IDSConnection}. After that a diagram is created from the given
    * {@link IDSConnection} and the diagram model is compared with the current
    * and expected {@link IDSConnection}.
    * @param expectedConnection The expected {@link IDSConnection}.
    * @param currentConnection The current {@link IDSConnection}.
    * @param modelFile The model file to create.
    * @param diagramFile The diagram file to create.
    * @throws CoreException Occurred Exception
    * @throws DSException Occurred Exception
    */
   public static void compareModels(IDSConnection expectedConnection,
                                    IDSConnection currentConnection,
                                    IFile modelFile,
                                    IFile diagramFile) throws CoreException, DSException {
      // Compare connection with expected connection
      TestGenerationUtil.compareConnection(expectedConnection, currentConnection);
      // Create model
      CreateOperation co = new CreateOperation(currentConnection, modelFile, diagramFile);
      co.execute(null, false);
      // Open model
      DbcModel model = TestGenerationUtil.openDbcModel(modelFile);
      // Compare created model with connection
      TestGenerationUtil.compareModel(currentConnection, model);
      // Test finder on KeY connections
      TestInteractiveProvingUtil.findAllElements(model, expectedConnection);
      TestInteractiveProvingUtil.findAllElements(model, currentConnection);
   }

   /**
    * Closes the {@link MainWindow} {@link JFrame} via the main menu.
    * @param frame The {@link SwingBotJFrame} to close.
    */
   public static void closeKeyMain(SwingBotJFrame frame) {
      TestCase.assertTrue(frame.isOpen());
      SwingBotJMenuBar bar = frame.bot().jMenuBar();
      bar.menu("File").item("Exit").click();
      SwingBotJDialog dialog = frame.bot().jDialog("Exit");
      
      
      dialog.bot().jButton(UIManager.get("OptionPane.yesButtonText").toString()).clickAndWait();
      frame.bot().waitUntil(Conditions.componentCloses(dialog));
      TestCase.assertFalse(dialog.isOpen());
      frame.bot().waitUntil(Conditions.componentCloses(frame));
      TestCase.assertFalse(frame.isOpen());
   }

   /**
    * Returns the {@link SwingBotJFrame} for an KeY main window that
    * edits the given {@link IResource}.
    * @param resource The {@link IResource} to edit.
    * @return The found {@link SwingBotJFrame}.
    */
   public static SwingBotJFrame getInteractiveKeyMain(IResource resource) {
      SwingBot bot = new SwingBot();
      SwingBotJFrame frame = bot.jFrame(KeYResourceManager.getManager().getUserInterfaceTitle());
      TestCase.assertTrue(frame.isOpen());
      return frame;
   }
   
   /**
    * Implementations of this interface are used in {@link TestKeyUtil#testOpenProof(String, String, IDSProvableSelector, String, String, boolean, MethodTreatment, IDSProvableReferenceSelector)}
    * to select an {@link IDSProvable} to test.
    * @author Martin Hentschel
    */
   public static interface IDSProvableSelector {
      /**
       * Selects the {@link IDSProvable} to test.
       * @param con The opened {@link IDSConnection}.
       * @return The selected {@link IDSProvable}.
       * @throws DSException Occurred Exception.
       */
      public IDSProvable getProvable(IDSConnection con) throws DSException;
   }
   
   /**
    * Implementations searches the expected {@link IDSProvableReference} when
    * the proof is automatically finished.
    * @author Martin Hentschel
    */
   public static interface IDSProvableReferenceSelector {
      /**
       * The expected {@link IDSProvableReference}s.
       * @param con The {@link IDSConnection} to use to detect the references.
       * @return The expected {@link IDSProvableReference}s per event.
       * @throws DSException Occurred Exception.
       */
      public <T extends IDSProvableReference> List<List<T>> getExpectedProofReferences(IDSConnection con) throws DSException;
   }
   
   /**
    * Tests {@link IDSProvable#openInteractiveProof(String)} with the following steps:
    * <ol>
    *    <li>Open proof (no other proof loaded)</li>
    *    <li>Deselect proof</li>
    *    <li>Open proof again (proof should be selected)</li>
    *    <li>Open proof again (proof should still be selected)</li>
    *    <li>Remove proof task</li>
    *    <li>Open proof again (new proof should be open)</li>
    * </ol>
    * @param projectName The project name to use.
    * @param selector The {@link IDSProvable} to select the {@link IDSProvable} to test.
    * @param proofObligation The proof obligation to test.
    * @param expectedProofName The expected name of the opened proof.
    */
   public static void testOpenProof(String projectName,
                                    String pathInPlugin,
                                    IDSProvableSelector selector,
                                    String proofObligation,
                                    String expectedProofName,
                                    boolean automaticCloseable,
                                    MethodTreatment methodTreatment,
                                    IDSProvableReferenceSelector expectedReferenceSelector,
                                    boolean withInitialReferences) {
      KeyConnection connection = null;
      ConnectionLogger logger = new ConnectionLogger();
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      LoggingKeYConnectionListener listener = new LoggingKeYConnectionListener();
      try {
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * 2;
         // Create project and fill it with test data
         IProject project = TestUtilsUtil.createProject(projectName);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathInPlugin, project);
         // Open connection
         File location = ResourceUtil.getLocation(project); 
         TestCase.assertNotNull(location);
         TestCase.assertTrue(location.exists() && location.isDirectory());
         connection = createKeyConnection(true, location, DSPackageManagement.NO_PACKAGES, logger);
         TestCase.assertTrue(connection.isConnected());
         TestDataSourceUtil.compareConnectionEvents(connection, logger, true, false, false);
         // Get interactive frame
         SwingBotJFrame frame = getInteractiveKeyMain(project);
         // Get provable to open
         TestCase.assertNotNull(selector);
         IDSProvable provable = selector.getProvable(connection);
         // Open interactive proof
         TestCase.assertFalse(connection.hasKeYConnectionListener(listener));
         connection.addKeYConnectionListener(listener);
         TestCase.assertTrue(connection.hasKeYConnectionListener(listener));
         TestCase.assertFalse(provable.hasInteractiveProof(proofObligation));
         KeyProof proof = openInteractiveProof(provable, proofObligation);
         TestCase.assertTrue(provable.hasInteractiveProof(proofObligation));
         listener.assertInteractiveProofStartedEvents(new KeYConnectionEvent(connection, proof));
         // Test initial references
         compareInitialProofReferences(provable, proofObligation, withInitialReferences);
         // Make sure that proof was opened
         SwingBotJTree tree = frame.bot().jTree(TaskTreeModel.class);
         checkSelectedProofOnSingleProofModel(tree, expectedProofName);
         // Unselect proof
         tree.unselectAll();
         TestCase.assertEquals(0, tree.getSelectedObjects().length);
         // Open proof again
         TestCase.assertTrue(provable.hasInteractiveProof(proofObligation));
         provable.openInteractiveProof(proofObligation); // No thread required, because nothing should be done.
         frame.bot().waitUntil(Conditions.hasSelection(tree));
         TestCase.assertTrue(provable.hasInteractiveProof(proofObligation));
         // Make sure that proof was selected again and that no new proof was opened.
         checkSelectedProofOnSingleProofModel(tree, expectedProofName);
         // Open proof again
         TestCase.assertTrue(provable.hasInteractiveProof(proofObligation));
         provable.openInteractiveProof(proofObligation); // No thread required, because nothing should be done.
         frame.bot().waitUntil(Conditions.hasSelection(tree));
         TestCase.assertTrue(provable.hasInteractiveProof(proofObligation));
         // Make sure that proof is still selected and that no new proof was opened.
         checkSelectedProofOnSingleProofModel(tree, expectedProofName);
         // Close task
         TestCase.assertTrue(connection instanceof KeyConnection);
         KeyConnection kc = (KeyConnection)connection;
         kc.closeTaskWithoutInteraction();
         frame.bot().waitWhile(Conditions.hasSelection(tree));
         TestCase.assertEquals(0, tree.getSelectedObjects().length);
         TestCase.assertEquals(0, tree.getModel().getChildCount(tree.getModel().getRoot()));
         // Open interactive proof
         TestCase.assertFalse(provable.hasInteractiveProof(proofObligation));
         proof = openInteractiveProof(provable, proofObligation);
         TestCase.assertTrue(provable.hasInteractiveProof(proofObligation));
         listener.assertInteractiveProofStartedEvents(new KeYConnectionEvent(connection, proof));
         // Test initial references
         compareInitialProofReferences(provable, proofObligation, withInitialReferences);
         // Make sure that proof was opened
         frame.bot().waitUntil(Conditions.hasSelection(tree));
         checkSelectedProofOnSingleProofModel(tree, expectedProofName);
         // Finish proof automatically
         proof = (KeyProof)provable.getInteractiveProof(proofObligation);
         TestCase.assertNotNull(proof);
         if (automaticCloseable) {
            TestCase.assertEquals(0, proof.getProofListeners().length);
            ProofLogger proofLogger = new ProofLogger();
            proof.addProofListener(proofLogger);
            TestCase.assertEquals(1, proof.getProofListeners().length);
            TestCase.assertEquals(0, proofLogger.getClosedEvents().size());
            TestCase.assertEquals(0, proofLogger.getReferenceChangedEvents().size());
            TestUtilsUtil.keyFinishSelectedProofAutomatically(frame, methodTreatment);
            TestCase.assertTrue(proof.isClosed());
            TestCase.assertEquals(1, proofLogger.getClosedEvents().size());
            TestCase.assertEquals(proof, proofLogger.getClosedEvents().get(0).getSource());
            TestCase.assertNull(proofLogger.getClosedEvents().get(0).getNewReferences());
            if (expectedReferenceSelector != null) {
               List<List<IDSProvableReference>> expectedReferences = expectedReferenceSelector.getExpectedProofReferences(connection);
               TestCase.assertNotNull(expectedReferences);
               TestCase.assertEquals(expectedReferences.size(), proofLogger.getReferenceChangedEvents().size());
               Iterator<List<IDSProvableReference>> expectedIter = expectedReferences.iterator();
               Iterator<DSProofEvent> currentIter = proofLogger.getReferenceChangedEvents().iterator();
               List<IDSProvableReference> nextExpected = null; // Will finally contain the last element
               while (expectedIter.hasNext() && currentIter.hasNext()) {
                  nextExpected = expectedIter.next();
                  DSProofEvent nextCurrent = currentIter.next();
                  TestCase.assertEquals(proof, nextCurrent.getSource());
                  compareProvableReferences(nextExpected, nextCurrent.getNewReferences());
               }
               TestCase.assertFalse(expectedIter.hasNext());
               TestCase.assertFalse(currentIter.hasNext());
               compareProvableReferences(nextExpected, proof.getProofReferences());
            }
            TestCase.assertEquals(1, proof.getProofListeners().length);
            proof.removeProofListener(proofLogger);
            TestCase.assertEquals(0, proof.getProofListeners().length);
         }
         TestCase.assertTrue(provable.hasInteractiveProof(proofObligation));
         // Close interactive frame
         closeKeyMain(frame);
         //Check connection and events
         TestDataSourceUtil.compareConnectionEvents(connection, logger, false, false, true);
         connection.removeConnectionListener(logger);
         TestCase.assertEquals(0, connection.getConnectionListeners().length);
         connection = null;
      }
      catch (CoreException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      catch (DSCanceledException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      finally {
         SWTBotPreferences.TIMEOUT = originalTimeout;
         try {
            if (connection != null) {
               TestCase.assertTrue(connection.hasKeYConnectionListener(listener));
               connection.removeKeYConnectionListener(listener);
               TestCase.assertFalse(connection.hasKeYConnectionListener(listener));
            }
            if (connection != null && connection.isConnected()) {
               TestGenerationUtil.closeConnection(connection);
               TestDataSourceUtil.compareConnectionEvents(connection, logger, false, false, true);
               connection.removeConnectionListener(logger);
               TestCase.assertEquals(0, connection.getConnectionListeners().length);
            }
         }
         catch (DSException e) {
            e.printStackTrace();
            fail(e.getMessage());
         }
      }
   }
   
   private static class LoggingKeYConnectionListener implements IKeYConnectionListener {
      private List<KeYConnectionEvent> interactiveProofStartedEvents = new LinkedList<KeYConnectionEvent>();

      @Override
      public void interactiveProofStarted(KeYConnectionEvent e) {
         interactiveProofStartedEvents.add(e);
      }
      
      public void assertInteractiveProofStartedEvents(KeYConnectionEvent... events) {
         assertEquals(interactiveProofStartedEvents.size(), events.length);
         int i = 0;
         for (KeYConnectionEvent current : interactiveProofStartedEvents) {
            assertEquals(current.getProof(), events[i].getProof());
            assertEquals(current.getSource(), events[i].getSource());
            i++;
         }
         interactiveProofStartedEvents.clear();
      }
   }
   
   /**
    * Compares the initial proof references.
    * @param provable The provable to check.
    * @param proofObligation The used obligation.
    * @param withReferences Initial references expected?
    * @throws DSException Occurred Exception
    */
   protected static void compareInitialProofReferences(IDSProvable provable, 
                                                       String proofObligation, 
                                                       boolean withReferences) throws DSException {
      IDSProof proof = provable.getInteractiveProof(proofObligation);
      TestCase.assertNotNull(proof);
      TestCase.assertTrue(proof.getProofReferences().isEmpty());
   }

   /**
    * Compares the provable references.
    * @param expected The expected references.
    * @param current The current references.
    */
   public static void compareProvableReferences(List<IDSProvableReference> expected, List<IDSProvableReference> current) {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.size(), current.size());
      Iterator<IDSProvableReference> expectedIter = expected.iterator();
      Iterator<IDSProvableReference> currentIter = current.iterator();
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         IDSProvableReference nextExpected = expectedIter.next();
         IDSProvableReference nextCurrent = currentIter.next();
         TestCase.assertEquals(nextExpected.getLabel(), nextCurrent.getLabel());
         TestCase.assertEquals(nextExpected.getTargetProvable(), nextCurrent.getTargetProvable());
      }
      TestCase.assertFalse(expectedIter.hasNext());
      TestCase.assertFalse(currentIter.hasNext());
   }
   
   /**
    * Blocks the current thread until the given {@link Thread} is no longer running.
    * @param thread The {@link Thread} to wait for.
    */
   protected static void waitForThread(Thread thread) {
      if (thread != null) {
         while (thread.isAlive()) {
            try {
               Thread.sleep(100);
            }
            catch (InterruptedException e) {
            }
         }
      }
   }
   
   /**
    * Closes the select a super type dialog.
    * @param frame The parent frame.
    * @param withSupertypeReference Select a supertype in model?
    */   
   public static void closeSelectASupertypeDialog(SwingBotJFrame frame, boolean withSupertypeReference) {
      SwingBotJDialog supertypeDialog = frame.bot().jDialog("Please select a supertype");
      SwingBotJList list = supertypeDialog.bot().jList();
      if (withSupertypeReference) {
         list.select(list.component.getModel().getSize() - 1);
      }
      else {
         list.select(0);
      }
      supertypeDialog.bot().waitUntil(Conditions.hasSelection(list));
      supertypeDialog.bot().jButton("OK").click();
      supertypeDialog.bot().waitUntil(Conditions.componentCloses(supertypeDialog));
      TestCase.assertFalse(supertypeDialog.isOpen());   
   }

   /**
    * Opens all opened dialogs when proof obligation {@link DefaultPOProvider#PRESERVES_GUARD} is used.
    * @param frame The parent frame.
    */
   public static void closeGuardDialogs(SwingBotJFrame frame) {
      // Closed guarded invariants
      SwingBotJDialog guardedInvariatnsDialog = frame.bot().jDialog("Please select the guarded invariants");
      guardedInvariatnsDialog.bot().jButton("OK").click();
      guardedInvariatnsDialog.bot().waitUntil(Conditions.componentCloses(guardedInvariatnsDialog));
      TestCase.assertFalse(guardedInvariatnsDialog.isOpen()); 
      // Closed guard 
      SwingBotJDialog guardDialog = frame.bot().jDialog("Please select the guard");
      SwingBotJList list = guardDialog.bot().jList();
      list.selectByText(Object.class.getCanonicalName());
      guardDialog.bot().waitUntil(Conditions.hasSelection(list));
      guardDialog.bot().jButton("OK").click();
      guardDialog.bot().waitUntil(Conditions.componentCloses(guardDialog));
      TestCase.assertFalse(guardDialog.isOpen());
      // Close depends dialogs
      try {
         while (!frame.bot().jDialogsWithPrefix("Depends clause for \"").isEmpty()) {
            SwingBotJDialog dependsDialog = frame.bot().jDialogWithPrefix("Depends clause for \"");
            dependsDialog.bot().jButton("OK").click();
            dependsDialog.bot().waitUntil(Conditions.componentCloses(dependsDialog));
            TestCase.assertFalse(dependsDialog.isOpen());
         }
      }
      catch (WidgetNotFoundException e) {
         // No more existing dialogs, can continue now
      }
   }

   /**
    * Closes the contract configurator.
    * @param frame The parent frame.
    * @param withInitialReferences Add initial references?
    */
   public static void closeContractConfigurator(SwingBotJFrame frame, boolean withInitialReferences) {
      SwingBotJDialog contractConfigurationDialog = frame.bot().jDialog("Contract Configurator");
      SwingBotJTabbedPane tabPane = contractConfigurationDialog.bot().jTabbedPane();
      // Unselect assumed invariants
      if (!withInitialReferences) {
         int assumedIndex = tabPane.indexOfTitle("Assumed Invariants");
         if (assumedIndex >= 0) {
            AbstractSwingBotComponent<? extends Component> pane = tabPane.select(assumedIndex);
            SwingBotJButton unselectButton = pane.bot().jButton("Unselect all");
            unselectButton.clickAndWait();
         }
         // Unselect assumed invariants
         int ensuredIndex = tabPane.indexOfTitle("Ensured Invariants");
         if (ensuredIndex >= 0) {
            AbstractSwingBotComponent<? extends Component> pane = tabPane.select(ensuredIndex);
            SwingBotJButton unselectButton = pane.bot().jButton("Unselect all");
            unselectButton.clickAndWait();
         }
      }
      // Close dialog
      contractConfigurationDialog.bot().jButton("OK").click();
      contractConfigurationDialog.bot().waitUntil(Conditions.componentCloses(contractConfigurationDialog));
      TestCase.assertFalse(contractConfigurationDialog.isOpen());   
   }

   /**
    * Makes sure that the correct proof is selected.
    * @param tree The tree.
    * @param expectedProofName The name of the expected proof.
    */
   public static void checkSelectedProofOnSingleProofModel(SwingBotJTree tree,
                                                           String expectedProofName) {
      TreeModel model = tree.getModel();
      TestCase.assertEquals(1, model.getChildCount(model.getRoot()));
      Object[] selectedObjects = tree.getSelectedObjects();
      TestCase.assertEquals(1, selectedObjects.length);
      TestCase.assertTrue(selectedObjects[0] instanceof TaskTreeNode);
      Proof proof = ((TaskTreeNode)selectedObjects[0]).proof();
      TestCase.assertEquals(expectedProofName, proof.name().toString());
   }

   /**
    * Opens the interactive proof by calling {@link IDSProvable#openInteractiveProof(String)}
    * from a new created {@link Thread}.
    * @param provable The {@link IDSProvable} to execute on.
    * @param obligation The proof obligation to use.
    */
   public static KeyProof openInteractiveProof(IDSProvable provable, String obligation) {
      OpenInteractiveProofThread thread = new OpenInteractiveProofThread(provable, obligation);
      thread.start();
      waitForThread(thread);
      IDSProof result = thread.getOpenedProof();
      TestCase.assertTrue(result instanceof KeyProof);
      return (KeyProof)result;
   }
   
   /**
    * Utility {@link Thread} used by {@link TestKeyUtil#openInteractiveProof(IDSProvable, String)}
    * to instantiate an interactive proof.
    * @author Martin Hentschel
    */
   private static class OpenInteractiveProofThread extends Thread {
      /**
       * The target provable.
       */
      private IDSProvable provable;
      
      /**
       * The proof obligation.
       */
      private String obligation;
      
      /**
       * The opened {@link IDSProof}.
       */
      private IDSProof openedProof;
      
      /**
       * Constructor.
       * @param provable The target provable.
       * @param obligation The proof obligation.
       */
      public OpenInteractiveProofThread(IDSProvable provable, String obligation) {
         this.provable = provable;
         this.obligation = obligation;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void run() {
         try {
            openedProof = provable.openInteractiveProof(obligation);
         }
         catch (Exception e) {
            e.printStackTrace();
         }
      }

      /**
       * Returns the oepend {@link IDSProof}.
       * @return The opened {@link IDSProof}.
       */
      public IDSProof getOpenedProof() {
         return openedProof;
      }
   }
}