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

package de.hentschel.visualdbc.datasource.key.test.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.key_project.key4eclipse.starter.core.job.AbstractKeYMainWindowJob;
import org.key_project.swtbot.swing.bot.SwingBot;
import org.key_project.swtbot.swing.bot.SwingBotJDialog;
import org.key_project.swtbot.swing.bot.SwingBotJFrame;
import org.key_project.swtbot.swing.bot.SwingBotJMenuBar;
import org.key_project.swtbot.swing.bot.SwingBotJTree;
import org.key_project.swtbot.swing.bot.finder.waits.Conditions;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
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
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.event.DSProofEvent;
import de.hentschel.visualdbc.datasource.model.exception.DSCanceledException;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.AbstractMemoryType;
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
import de.hentschel.visualdbc.datasource.model.memory.MemoryOperationContract;
import de.hentschel.visualdbc.datasource.model.memory.MemoryPackage;
import de.hentschel.visualdbc.datasource.test.util.ConnectionLogger;
import de.hentschel.visualdbc.datasource.test.util.TestDataSourceUtil;
import de.hentschel.visualdbc.datasource.util.DriverUtil;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcType;
import de.hentschel.visualdbc.dbcmodel.DbCAxiomContract;
import de.hentschel.visualdbc.dbcmodel.DbcAttribute;
import de.hentschel.visualdbc.dbcmodel.DbcAxiom;
import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcConstructor;
import de.hentschel.visualdbc.dbcmodel.DbcEnum;
import de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral;
import de.hentschel.visualdbc.dbcmodel.DbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcInvariant;
import de.hentschel.visualdbc.dbcmodel.DbcMethod;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcPackage;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcVisibility;
import de.hentschel.visualdbc.generation.operation.CreateOperation;
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.hentschel.visualdbc.interactive.proving.ui.test.util.TestInteractiveProvingUtil;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.TaskTreeModel;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
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
      boolean usePrettyPrinting = SymbolicExecutionUtil.isUsePrettyPrinting();
      try {
         // Disable pretty printing to make tests more robust against different term representations
         SymbolicExecutionUtil.setUsePrettyPrinting(false);
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
         SymbolicExecutionUtil.setUsePrettyPrinting(usePrettyPrinting);
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
   
   /**
    * <p>
    * Converts the given {@link DbcModel} into an {@link IDSConnection}.
    * </p>
    * <p>
    * Proofs are not supported!
    * </p>
    * @param model The {@link DbcModel} to convert.
    * @return The {@link IDSConnection} with the same content as the given {@link DbcModel}.
    */
   public static IDSConnection convertModelToConnection(DbcModel model) {
      Map<DbcClass, MemoryClass> convertedClassMap = new HashMap<DbcClass, MemoryClass>();
      Map<DbcInterface, MemoryInterface> convertedInterfaceMap = new HashMap<DbcInterface, MemoryInterface>();
      MemoryConnection dsCon = new MemoryConnection();
      for (DbcPackage dbcPackage : model.getPackages()) {
         MemoryPackage dsPackage = createPackage(convertedInterfaceMap, convertedClassMap, dbcPackage);
         dsCon.addPackage(dsPackage);
      }
      addTypes(convertedInterfaceMap, convertedClassMap, dsCon, model.getTypes());
      return dsCon;
   }

   /**
    * Converts the given {@link DbcPackage}s into {@link MemoryPackage}s and adds them to the parent.
    * @param convertedInterfaceMap Maps an {@link DbcInterface} to its {@link MemoryInterface} representation.
    * @param convertedClassMap Maps a {@link DbcClass} to its {@link MemoryClass} representation.
    * @param dsPackage The {@link MemoryPackage} to add child packages to.
    * @param dbcPackages The child packages to add.
    */
   private static void addPackages(Map<DbcInterface, MemoryInterface> convertedInterfaceMap, 
                                   Map<DbcClass, MemoryClass> convertedClassMap, 
                                   MemoryPackage dsPackage, 
                                   List<DbcPackage> dbcPackages) {
      for (DbcPackage dbcPackage : dbcPackages) {
         MemoryPackage dsChildPackage = createPackage(convertedInterfaceMap, convertedClassMap, dbcPackage);
         dsPackage.addPackage(dsChildPackage);
      }
   }

   /**
    * Creates a {@link MemoryPackage} for the given {@link DbcPackage} with same content. 
    * @param convertedInterfaceMap Maps an {@link DbcInterface} to its {@link MemoryInterface} representation.
    * @param convertedClassMap Maps a {@link DbcClass} to its {@link MemoryClass} representation.
    * @param dbcPackage The {@link DbcPackage} to convert.
    * @return The created {@link MemoryPackage}.
    */
   private static MemoryPackage createPackage(Map<DbcInterface, MemoryInterface> convertedInterfaceMap, 
                                              Map<DbcClass, MemoryClass> convertedClassMap, 
                                              DbcPackage dbcPackage) {
      MemoryPackage dsPackage = new MemoryPackage(dbcPackage.getName());
      addPackages(convertedInterfaceMap, convertedClassMap, dsPackage, dbcPackage.getPackages());
      addTypes(convertedInterfaceMap, convertedClassMap, dsPackage, dbcPackage.getTypes());
      return dsPackage;
   }

   /**
    * Converts the given {@link AbstractDbcType}s into {@link AbstractMemoryType}s and adds them to the parent.
    * @param convertedInterfaceMap Maps an {@link DbcInterface} to its {@link MemoryInterface} representation.
    * @param convertedClassMap Maps a {@link DbcClass} to its {@link MemoryClass} representation.
    * @param dsCon The {@link MemoryConnection} to add child packages to.
    * @param dbcTypes The child types to add.
    */
   private static void addTypes(Map<DbcInterface, MemoryInterface> convertedInterfaceMap, 
                                Map<DbcClass, MemoryClass> convertedClassMap, 
                                MemoryConnection dsCon, 
                                List<AbstractDbcType> dbcTypes) {
      for (AbstractDbcType dbcType : dbcTypes) {
         if (dbcType instanceof DbcClass) {
            MemoryClass dsClass = createClass(convertedInterfaceMap, convertedClassMap, (DbcClass)dbcType);
            dsCon.addClass(dsClass);
         }
         else if (dbcType instanceof DbcInterface) {
            MemoryInterface dsInterface = createInterface(convertedInterfaceMap, convertedClassMap, (DbcInterface)dbcType);
            dsCon.addInterface(dsInterface);
         }
         else if (dbcType instanceof DbcEnum) {
            MemoryEnum dsEnum = createEnum(convertedInterfaceMap, convertedClassMap, (DbcEnum)dbcType);
            dsCon.addEnum(dsEnum);
         }
         else {
            fail("Unknown type \"" + dbcType + "\".");
         }
      }
   }

   /**
    * Converts the given {@link AbstractDbcType}s into {@link AbstractMemoryType}s and adds them to the parent.
    * @param convertedInterfaceMap Maps an {@link DbcInterface} to its {@link MemoryInterface} representation.
    * @param convertedClassMap Maps a {@link DbcClass} to its {@link MemoryClass} representation.
    * @param dsPackage The {@link MemoryPackage} to add child packages to.
    * @param dbcTypes The child types to add.
    */
   private static void addTypes(Map<DbcInterface, MemoryInterface> convertedInterfaceMap, 
                                Map<DbcClass, MemoryClass> convertedClassMap, 
                                MemoryPackage dsPackage, 
                                List<AbstractDbcType> dbcTypes) {
      for (AbstractDbcType dbcType : dbcTypes) {
         if (dbcType instanceof DbcClass) {
            MemoryClass dsClass = createClass(convertedInterfaceMap, convertedClassMap, (DbcClass)dbcType);
            dsPackage.addClass(dsClass);
         }
         else if (dbcType instanceof DbcInterface) {
            MemoryInterface dsInterface = createInterface(convertedInterfaceMap, convertedClassMap, (DbcInterface)dbcType);
            dsPackage.addInterface(dsInterface);
         }
         else if (dbcType instanceof DbcEnum) {
            MemoryEnum dsEnum = createEnum(convertedInterfaceMap, convertedClassMap, (DbcEnum)dbcType);
            dsPackage.addEnum(dsEnum);
         }
         else {
            fail("Unknown type \"" + dbcType + "\".");
         }
      }
   }

   /**
    * Converts the given {@link AbstractDbcType}s into {@link AbstractMemoryType}s and adds them to the parent.
    * @param convertedInterfaceMap Maps an {@link DbcInterface} to its {@link MemoryInterface} representation.
    * @param convertedClassMap Maps a {@link DbcClass} to its {@link MemoryClass} representation.
    * @param dsType The {@link AbstractMemoryType} to add child packages to.
    * @param dbcTypes The child types to add.
    */
   private static void addTypes(Map<DbcInterface, MemoryInterface> convertedInterfaceMap, 
                                Map<DbcClass, MemoryClass> convertedClassMap, 
                                AbstractMemoryType dsType, 
                                List<AbstractDbcType> dbcTypes) {
      for (AbstractDbcType dbcType : dbcTypes) {
         if (dbcType instanceof DbcClass) {
            MemoryClass dsClass = createClass(convertedInterfaceMap, convertedClassMap, (DbcClass)dbcType);
            dsType.addInnerClass(dsClass);
         }
         else if (dbcType instanceof DbcInterface) {
            MemoryInterface dsInterface = createInterface(convertedInterfaceMap, convertedClassMap, (DbcInterface)dbcType);
            dsType.addInnerInterface(dsInterface);
         }
         else if (dbcType instanceof DbcEnum) {
            MemoryEnum dsEnum = createEnum(convertedInterfaceMap, convertedClassMap, (DbcEnum)dbcType);
            dsType.addInnerEnum(dsEnum);
         }
         else {
            fail("Unknown type \"" + dbcType + "\".");
         }
      }
   }

   /**
    * Creates a {@link MemoryInterface} for the given {@link DbcInterface} with same content. 
    * @param convertedInterfaceMap Maps an {@link DbcInterface} to its {@link MemoryInterface} representation.
    * @param convertedClassMap Maps a {@link DbcClass} to its {@link MemoryClass} representation.
    * @param dbcInterface The {@link DbcInterface} to convert.
    * @return The created {@link MemoryInterface}.
    */
   private static MemoryInterface createInterface(Map<DbcInterface, MemoryInterface> convertedInterfaceMap, 
                                                  Map<DbcClass, MemoryClass> convertedClassMap, 
                                                  DbcInterface dbcInterface) {
      MemoryInterface dsInterface = convertedInterfaceMap.get(dbcInterface);
      if (dsInterface == null) {
         dsInterface = new MemoryInterface(dbcInterface.getName(), 
                                           toDSVisibility(dbcInterface.getVisibility()));
         dsInterface.setStatic(dbcInterface.isStatic());
         for (DbcMethod dbcMethod : dbcInterface.getMethods()) {
            MemoryMethod dsMethod = createMethod(dbcMethod);
            dsInterface.addMethod(dsMethod);
         }
         for (DbcAttribute dbcAttribute : dbcInterface.getAttributes()) {
            MemoryAttribute dsAttribute = createAttribute(dbcAttribute);
            dsInterface.addAttribute(dsAttribute);
         }
         for (DbcInterface dbcExtendInterface : dbcInterface.getExtends()) {
            MemoryInterface dsExtendInterface = createInterface(convertedInterfaceMap, convertedClassMap, dbcExtendInterface);
            dsInterface.getExtends().add(dsExtendInterface);
         }
         for (String fullName : dbcInterface.getExtendsFullNames()) {
            dsInterface.getExtendsFullnames().add(fullName);
         }
         for (DbcInvariant dbcInvariant : dbcInterface.getInvariants()) {
            MemoryInvariant dsInvariant = createInvariant(dbcInvariant);
            dsInterface.addInvariant(dsInvariant);
         }
         for (DbcAxiom dbcAxiom : dbcInterface.getAxioms()) {
            MemoryAxiom dsAxiom = createAxiom(dbcAxiom);
            dsInterface.addAxiom(dsAxiom);
         }
         addTypes(convertedInterfaceMap, convertedClassMap, dsInterface, dbcInterface.getTypes());
         convertedInterfaceMap.put(dbcInterface, dsInterface);
      }
      return dsInterface;
   }

   /**
    * Creates a {@link MemoryClass} for the given {@link DbcClass} with same content. 
    * @param convertedInterfaceMap Maps an {@link DbcInterface} to its {@link MemoryInterface} representation.
    * @param convertedClassMap Maps a {@link DbcClass} to its {@link MemoryClass} representation.
    * @param dbcClass The {@link DbcClass} to convert.
    * @return The created {@link MemoryClass}.
    */
   private static MemoryClass createClass(Map<DbcInterface, MemoryInterface> convertedInterfaceMap, 
                                          Map<DbcClass, MemoryClass> convertedClassMap, 
                                          DbcClass dbcClass) {
      MemoryClass dsClass = convertedClassMap.get(dbcClass);
      if (dsClass == null) {
         dsClass = new MemoryClass(dbcClass.getName(),
                                   toDSVisibility(dbcClass.getVisibility()), 
                                   dbcClass.isAbstract(),
                                   dbcClass.isFinal());
         dsClass.setAnonymous(dbcClass.isAnonymous());
         dsClass.setStatic(dbcClass.isStatic());
         for (DbcConstructor dbcConstructor : dbcClass.getConstructors()) {
            MemoryConstructor dsConstructor = createConstructor(dbcConstructor);
            dsClass.addConstructor(dsConstructor);
         }
         for (DbcMethod dbcMethod : dbcClass.getMethods()) {
            MemoryMethod dsMethod = createMethod(dbcMethod);
            dsClass.addMethod(dsMethod);
         }
         for (DbcAttribute dbcAttribute : dbcClass.getAttributes()) {
            MemoryAttribute dsAttribute = createAttribute(dbcAttribute);
            dsClass.addAttribute(dsAttribute);
         }
         for (DbcClass dbcExtendClass : dbcClass.getExtends()) {
            MemoryClass dsExtendClass = createClass(convertedInterfaceMap, convertedClassMap, dbcExtendClass);
            dsClass.getExtends().add(dsExtendClass);
         }
         for (String fullName : dbcClass.getExtendsFullNames()) {
            dsClass.getExtendsFullnames().add(fullName);
         }
         for (DbcInterface dbcImplementsInterface : dbcClass.getImplements()) {
            MemoryInterface dsImplementsInterface = createInterface(convertedInterfaceMap, convertedClassMap, dbcImplementsInterface);
            dsClass.getImplements().add(dsImplementsInterface);
         }
         for (String fullName : dbcClass.getImplementsFullNames()) {
            dsClass.getImplementsFullnames().add(fullName);
         }
         for (DbcInvariant dbcInvariant : dbcClass.getInvariants()) {
            MemoryInvariant dsInvariant = createInvariant(dbcInvariant);
            dsClass.addInvariant(dsInvariant);
         }
         for (DbcAxiom dbcAxiom : dbcClass.getAxioms()) {
            MemoryAxiom dsAxiom = createAxiom(dbcAxiom);
            dsClass.addAxiom(dsAxiom);
         }
         addTypes(convertedInterfaceMap, convertedClassMap, dsClass, dbcClass.getTypes());
         convertedClassMap.put(dbcClass, dsClass);
      }
      return dsClass;
   }

   /**
    * Creates a {@link MemoryEnum} for the given {@link DbcEnum} with same content. 
    * @param convertedInterfaceMap Maps an {@link DbcInterface} to its {@link MemoryInterface} representation.
    * @param convertedClassMap Maps a {@link DbcClass} to its {@link MemoryClass} representation.
    * @param dbcEnum The {@link DbcEnum} to convert.
    * @return The created {@link MemoryEnum}.
    */
   private static MemoryEnum createEnum(Map<DbcInterface, MemoryInterface> convertedInterfaceMap, 
                                        Map<DbcClass, MemoryClass> convertedClassMap, 
                                        DbcEnum dbcEnum) {
      MemoryEnum dsEnum = new MemoryEnum(dbcEnum.getName(), 
                                         toDSVisibility(dbcEnum.getVisibility()));
      dsEnum.setStatic(dbcEnum.isStatic());
      for (DbcConstructor dbcConstructor : dbcEnum.getConstructors()) {
         MemoryConstructor dsConstructor = createConstructor(dbcConstructor);
         dsEnum.addConstructor(dsConstructor);
      }
      for (DbcMethod dbcMethod : dbcEnum.getMethods()) {
         MemoryMethod dsMethod = createMethod(dbcMethod);
         dsEnum.addMethod(dsMethod);
      }
      for (DbcAttribute dbcAttribute : dbcEnum.getAttributes()) {
         MemoryAttribute dsAttribute = createAttribute(dbcAttribute);
         dsEnum.addAttribute(dsAttribute);
      }
      for (DbcEnumLiteral dbcLiteral : dbcEnum.getLiterals()) {
         MemoryEnumLiteral dsLiteral = createEnumLiteral(dbcLiteral);
         dsEnum.addLiteral(dsLiteral);
      }
      for (DbcInvariant dbcInvariant : dbcEnum.getInvariants()) {
         MemoryInvariant dsInvariant = createInvariant(dbcInvariant);
         dsEnum.addInvariant(dsInvariant);
      }
      for (DbcAxiom dbcAxiom : dbcEnum.getAxioms()) {
         MemoryAxiom dsAxiom = createAxiom(dbcAxiom);
         dsEnum.addAxiom(dsAxiom);
      }
      for (DbcInterface dbcImplementsInterface : dbcEnum.getImplements()) {
         MemoryInterface dsImplementsInterface = createInterface(convertedInterfaceMap, convertedClassMap, dbcImplementsInterface);
         dsEnum.getImplements().add(dsImplementsInterface);
      }
      for (String fullName : dbcEnum.getImplementsFullNames()) {
         dsEnum.getImplementsFullnames().add(fullName);
      }
      addTypes(convertedInterfaceMap, convertedClassMap, dsEnum, dbcEnum.getTypes());
      return dsEnum;
   }

   /**
    * Creates a {@link MemoryEnumLiteral} for the given {@link DbcEnumLiteral} with same content. 
    * @param dbcLiteral The {@link DbcEnumLiteral} to convert.
    * @return The created {@link MemoryEnumLiteral}.
    */
   private static MemoryEnumLiteral createEnumLiteral(DbcEnumLiteral dbcLiteral) {
      MemoryEnumLiteral dsLiteral = new MemoryEnumLiteral(dbcLiteral.getName());
      return dsLiteral;
   }

   /**
    * Creates a {@link MemoryConstructor} for the given {@link DbcConstructor} with same content. 
    * @param dbcConstructor The {@link DbcConstructor} to convert.
    * @return The created {@link MemoryConstructor}.
    */
   private static MemoryConstructor createConstructor(DbcConstructor dbcConstructor) {
      MemoryConstructor dsConstructor = new MemoryConstructor(dbcConstructor.getSignature(), 
                                                              toDSVisibility(dbcConstructor.getVisibility()));
      for (DbcOperationContract dbcContract : dbcConstructor.getOperationContracts()) {
         MemoryOperationContract dsContract = createOperationContract(dbcContract);
         dsConstructor.addOperationContract(dsContract);
      }
      return dsConstructor;
   }
   
   /**
    * Creates a {@link MemoryMethod} for the given {@link DbcMethod} with same content. 
    * @param dbcMethod The {@link DbcMethod} to convert.
    * @return The created {@link MemoryMethod}.
    */
   private static MemoryMethod createMethod(DbcMethod dbcMethod) {
      MemoryMethod dsMethod = new MemoryMethod(dbcMethod.getSignature(), 
                                               dbcMethod.getReturnType(), 
                                               toDSVisibility(dbcMethod.getVisibility()), 
                                               dbcMethod.isStatic(), 
                                               dbcMethod.isFinal(), 
                                               dbcMethod.isAbstract());
      for (DbcOperationContract dbcContract : dbcMethod.getOperationContracts()) {
         MemoryOperationContract dsContract = createOperationContract(dbcContract);
         dsMethod.addOperationContract(dsContract);
      }
      return dsMethod;
   }

   /**
    * Creates a {@link MemoryOperationContract} for the given {@link DbcOperationContract} with same content. 
    * @param dbcContract The {@link DbcOperationContract} to convert.
    * @return The created {@link MemoryOperationContract}.
    */
   private static MemoryOperationContract createOperationContract(DbcOperationContract dbcContract) {
      MemoryOperationContract dsContract = new MemoryOperationContract(dbcContract.getName(), 
                                                                       dbcContract.getPre(), 
                                                                       dbcContract.getPost(), 
                                                                       dbcContract.getModifies(), 
                                                                       dbcContract.getTermination());
      for (DbcProofObligation dbcObligation : dbcContract.getProofObligations()) {
         dsContract.getObligations().add(dbcObligation.getObligation());
      }
      return dsContract;
   }

   /**
    * Creates a {@link MemoryAttribute} for the given {@link DbcAttribute} with same content. 
    * @param dbcAttribute The {@link DbcAttribute} to convert.
    * @return The created {@link MemoryAttribute}.
    */
   private static MemoryAttribute createAttribute(DbcAttribute dbcAttribute) {
      MemoryAttribute dsAttribute = new MemoryAttribute(dbcAttribute.getName(), 
                                                        dbcAttribute.getType(), 
                                                        toDSVisibility(dbcAttribute.getVisibility()), 
                                                        dbcAttribute.isStatic(), 
                                                        dbcAttribute.isFinal());
      return dsAttribute;
   }

   /**
    * Creates a {@link MemoryInvariant} for the given {@link DbcInvariant} with same content. 
    * @param dbcInvariant The {@link DbcInvariant} to convert.
    * @return The created {@link MemoryInvariant}.
    */
   private static MemoryInvariant createInvariant(DbcInvariant dbcInvariant) {
      MemoryInvariant dsInvariant = new MemoryInvariant(dbcInvariant.getName(), 
                                                        dbcInvariant.getCondition());
      return dsInvariant;
   }

   /**
    * Creates a {@link MemoryAxiom} for the given {@link DbcAxiom} with same content. 
    * @param dbcAxiom The {@link DbcAxiom} to convert.
    * @return The created {@link MemoryAxiom}.
    */
   private static MemoryAxiom createAxiom(DbcAxiom dbcAxiom) {
      MemoryAxiom dsAxiom = new MemoryAxiom(dbcAxiom.getName(), dbcAxiom.getDefinition());
      for (DbCAxiomContract dbcContract : dbcAxiom.getAxiomContracts()) {
         MemoryAxiomContract dsContract = createAxiomContract(dbcContract);
         dsAxiom.addAxiomContract(dsContract);
      }
      return dsAxiom;
   }

   /**
    * Creates a {@link MemoryAxiomContract} for the given {@link DbCAxiomContract} with same content. 
    * @param dbcContract The {@link DbCAxiomContract} to convert.
    * @return The created {@link MemoryAxiomContract}.
    */
   private static MemoryAxiomContract createAxiomContract(DbCAxiomContract dbcContract) {
      MemoryAxiomContract dsContract = new MemoryAxiomContract(dbcContract.getName(), 
                                                               dbcContract.getPre(), 
                                                               dbcContract.getDep());
      for (DbcProofObligation dbcObligation : dbcContract.getProofObligations()) {
         dsContract.getObligations().add(dbcObligation.getObligation());
      }
      return dsContract;
   }

   /**
    * Converts the {@link DbcVisibility} into a {@link DSVisibility}.
    * @param dbcVisibility The {@link DbcVisibility} to convert.
    * @return The {@link DSVisibility}.
    */
   private static DSVisibility toDSVisibility(DbcVisibility dbcVisibility) {
      switch (dbcVisibility) {
         case DEFAULT : return DSVisibility.DEFAULT;
         case PRIVATE : return DSVisibility.PRIVATE;
         case PROTECTED : return DSVisibility.PROTECTED;
         case PUBLIC : return DSVisibility.PUBLIC;
         default : fail("Unknown visibility \"" + dbcVisibility + "\".");
                   return null;
      }
   }
}