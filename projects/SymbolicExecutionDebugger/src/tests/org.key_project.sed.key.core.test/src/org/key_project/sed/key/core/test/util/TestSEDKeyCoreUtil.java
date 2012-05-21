package org.key_project.sed.key.core.test.util;

import java.io.IOException;
import java.util.List;

import javax.xml.parsers.ParserConfigurationException;

import junit.framework.TestCase;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.swt.widgets.Display;
import org.key_project.key4eclipse.test.util.TestKeY4EclipseUtil;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.core.model.serialization.SEDXMLReader;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.test.Activator;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;
import org.key_project.util.jdt.JDTUtil;
import org.xml.sax.SAXException;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

/**
 * Provides static methods that makes testing easier.
 * @author Martin Hentschel
 */
public final class TestSEDKeyCoreUtil {
   /**
    * Forbid instances.
    */
   private TestSEDKeyCoreUtil() {
   }
   
   /**
    * Launches the {@link IMethod} in the symbolic execution debugger
    * based on KeY.
    * @param method The {@link IMethod} to debug.
    * @param showMethodReturnValues Show method return values?
    * @throws Exception Occurred Exception.
    */
   public static void launchKeY(final IMethod method,
                                final boolean showMethodReturnValues) throws Exception {
      IRunnableWithException run = new AbstractRunnableWithException() {
         @Override
         public void run() {
            try {
               ILaunchConfiguration config = getKeYLaunchConfiguration(method);
               ILaunchConfigurationWorkingCopy wc = config.getWorkingCopy();
               wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES, showMethodReturnValues);
               config = wc.doSave();
               DebugUITools.launch(config, KeySEDUtil.MODE);
            }
            catch (Exception e) {
               setException(e);
            }
         }
      };
      Display.getDefault().syncExec(run);
      if (run.getException() != null) {
         throw run.getException();
      }
   }
   
   /**
    * Returns an {@link ILaunchConfiguration} for the given {@link IMethod}
    * that starts the symbolic execution debugger based on KeY.
    * @param method The {@link IMethod} to debug.
    * @return The {@link ILaunchConfiguration}.
    * @throws CoreException Occurred Exception.
    */
   public static ILaunchConfiguration getKeYLaunchConfiguration(IMethod method) throws CoreException {
      List<ILaunchConfiguration> configs = KeySEDUtil.searchLaunchConfigurations(method);
      if (!configs.isEmpty()) {
         return configs.get(0);
      }
      else {
         return KeySEDUtil.createConfiguration(method);
      }
   }

   /**
    * Creates an expected {@link ISEDDebugTarget} defined by the given bundle file.
    * @param expectedModelPathInBundle The path to the oracle file in the bundle.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws IOException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws ParserConfigurationException Occurred Exception.
    */   
   public static ISEDDebugTarget createExpectedModel(String expectedModelPathInBundle) throws ParserConfigurationException, SAXException, IOException {
      SEDXMLReader reader = new SEDXMLReader();
      List<ISEDDebugTarget> targets = reader.read(BundleUtil.openInputStream(Activator.PLUGIN_ID, expectedModelPathInBundle));
      TestCase.assertNotNull(targets);
      TestCase.assertEquals(1, targets.size());
      return targets.get(0);
   }
   
   /**
    * Creates the expected initial model that represents the state after
    * connecting to KeY with only one symbolic thread without any children.
    * @param targetName The expected name of the {@link ISEDDebugTarget}. 
    * @return The created expected model.
    */
   public static ISEDDebugTarget createExpectedInitialModel(String targetName) {
      // Create debug target
      SEDMemoryDebugTarget target = new SEDMemoryDebugTarget(null);
      target.setModelIdentifier(KeYDebugTarget.MODEL_IDENTIFIER);
      target.setName(targetName);
      // Add thread
      SEDMemoryThread thread = new SEDMemoryThread(target);
      thread.setName(IExecutionStartNode.DEFAULT_START_NODE_NAME);
      target.addSymbolicThread(thread);
      return target;
   }
   
   /**
    * Makes sure that the given {@link ISEDDebugTarget} is
    * in the initial state.
    * @param target The give {@link ISEDDebugTarget} to check.
    * @param targetName The expected name of the {@link ISEDDebugTarget}. 
    * @throws DebugException Occurred Exception.
    */
   public static void assertInitialTarget(ISEDDebugTarget target, String targetName) throws DebugException {
      TestSedCoreUtil.compareDebugTarget(createExpectedInitialModel(targetName), target, false);
   }
   
   /**
    * Makes sure that the given {@link ISEDDebugTarget} contains the
    * symbolic execution tree of the statement example.
    * @param target The give {@link ISEDDebugTarget} to check.
    * @throws DebugException Occurred Exception.
    * @throws IOException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws ParserConfigurationException Occurred Exception.
    */
   public static void assertFlatStepsExample(ISEDDebugTarget target) throws DebugException, ParserConfigurationException, SAXException, IOException {
      TestSedCoreUtil.compareDebugTarget(createExpectedModel("data/statements/oracle/FlatSteps.xml"), target, false);
   }
   
   /**
    * Computes the name of a {@link KeYDebugTarget} which debugs
    * the given {@link IMethod} with generated operation contract.
    * @param method The debuged {@link IMethod}.
    * @return The used target name in a {@link KeYDebugTarget} with generated operation contract.
    * @throws JavaModelException Occurred Exception
    */
   public static String computeTargetName(IMethod method) throws JavaModelException {
      TestCase.assertNotNull(method);
      return TestKeY4EclipseUtil.createOperationContractId(method.getDeclaringType().getElementName(), 
                                                           JDTUtil.getQualifiedMethodLabel(method).replaceAll(" ", StringUtil.EMPTY_STRING),
                                                           "-2147483648", 
                                                           "normal_behavior");
   }
}
