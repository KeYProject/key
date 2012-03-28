package org.key_project.sed.key.core.test.util;

import java.io.IOException;
import java.util.List;

import javax.xml.parsers.ParserConfigurationException;

import junit.framework.TestCase;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.core.model.serialization.SEDXMLReader;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.test.Activator;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;
import org.xml.sax.SAXException;

/**
 * Provides static methods that makes testing easier.
 * @author Martin Hentschel
 */
public final class TestSEDKeyCoreUtil {
   /**
    * The name of the {@link ISEDDebugTarget} used in the flat list example.
    */
   public static final String FLAT_STEPS_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / FlatSteps::doSomething]";
   
   /**
    * The name of the {@link ISEDDebugTarget} used in the method call hierarchy example.
    */
   public static final String METHOD_CALL_HIERARCHY_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / MethodHierarchyCallTest::main]";
   
   /**
    * The name of the {@link ISEDDebugTarget} used in the method call hierarchy with exception example.
    */
   public static final String METHOD_CALL_HIERARCHY_WITH_EXCEPTION_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / MethodHierarchyCallWithExceptionTest::main]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the method call parallel example.
    */
   public static final String METHOD_CALL_PARALLEL_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / MethodCallParallelTest::main]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the method call on object example.
    */
   public static final String METHOD_CALL_ON_OBJECT_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / MethodCallOnObject::main]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the method call with exception on object example.
    */
   public static final String METHOD_CALL_ON_OBJECT_WITH_EXCEPTION_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / MethodCallOnObjectWithException::main]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the simple if example.
    */
   public static final String SIMPLE_IF_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / SimpleIf::min]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the functional if example.
    */
   public static final String FUNCTIONAL_IF_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / FunctionalIf::min]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the complex flat steps example.
    */
   public static final String COMPLEX_FLAT_STEPS_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / ComplexFlatSteps::doSomething]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the complex if example.
    */
   public static final String COMPLEX_IF_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / ComplexIf::min]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the static method call example.
    */
   public static final String STATIC_METHOD_CALL_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / StaticMethodCall::main]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the try catch finally example.
    */
   public static final String TRY_CATCH_FINALLY_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / TryCatchFinally::tryCatchFinally]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the else if different variables example.
    */
   public static final String ELSE_IF_DIFFERENT_VARIABLES_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / ElseIfDifferentVariables::main]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the fixed recursive method call example.
    */
   public static final String FIXED_RECURSIVE_METHOD_CALL_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / FixedRecursiveMethodCallTest::decreaseValue]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the fixed method call format test example.
    */
   public static final String METHOD_CALL_FORMAT_TEST_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / MethodFormatTest::main]";

   /**
    * The name of the {@link ISEDDebugTarget} used in the else if test example.
    */
   public static final String ELSE_IF_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / ElseIfTest::elseIf]";
   
   /**
    * Forbid instances.
    */
   private TestSEDKeyCoreUtil() {
   }
   
   /**
    * Launches the {@link IMethod} in the symbolic execution debugger
    * based on KeY.
    * @param method The {@link IMethod} to debug.
    * @throws Exception Occurred Exception.
    */
   public static void launchKeY(final IMethod method) throws Exception {
      IRunnableWithException run = new AbstractRunnableWithException() {
         @Override
         public void run() {
            try {
               ILaunchConfiguration config = getKeYLaunchConfiguration(method);
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
      thread.setName(KeYDebugTarget.DEFAULT_THREAD_NAME);
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
      TestSedCoreUtil.compareDebugTarget(createExpectedInitialModel(targetName), target);
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
      TestSedCoreUtil.compareDebugTarget(createExpectedModel("data/statements/oracle/FlatSteps.xml"), target);
   }
}
