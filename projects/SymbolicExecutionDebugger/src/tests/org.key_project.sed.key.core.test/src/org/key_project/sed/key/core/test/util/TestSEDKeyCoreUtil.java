package org.key_project.sed.key.core.test.util;

import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IThread;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchNode;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;

/**
 * Provides static methods that makes testing easier.
 * @author Martin Hentschel
 */
public final class TestSEDKeyCoreUtil {
   /**
    * The name of the {@link ISEDDebugTarget} used in the flat list example.
    */
   public static final String STATEMENT_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / FlatSteps::doSomething]";
   
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
    * Makes sure that the given {@link ISEDDebugTarget} is
    * in the initial state.
    * @param target The give {@link ISEDDebugTarget} to check.
    * @param targetName The expected name of the {@link ISEDDebugTarget}. 
    * @throws DebugException Occurred Exception.
    */
   public static void assertInitialTarget(ISEDDebugTarget target, String targetName) throws DebugException {
      compareDebugTarget(createExpectedInitialModel(targetName), target);
   }
   
   /**
    * Creates the expected initial model that represents the state after
    * connecting to KeY with only one symbolic thread without any children.
    * @param targetName The expected name of the {@link ISEDDebugTarget}. 
    * @return The created expected model.
    */
   public static ISEDDebugTarget createExpectedInitialModel(String targetName) {
      // Create target
      SEDMemoryDebugTarget target = new SEDMemoryDebugTarget(null);
      target.setModelIdentifier(KeYDebugTarget.MODEL_IDENTIFIER);
      target.setName(targetName);
      // Create thread
      SEDMemoryThread thread = new SEDMemoryThread(target);
      thread.setName(KeYDebugTarget.DEFAULT_THREAD_NAME);
      target.addSymbolicThread(thread);
      return target;
   }
   
   /**
    * Makes sure that the given {@link ISEDDebugTarget} contains the
    * symbolic execution tree of the statement example.
    * @param target The give {@link ISEDDebugTarget} to check.
    * @throws DebugException Occurred Exception.
    */
   public static void assertStatementsExample(ISEDDebugTarget target) throws DebugException {
      compareDebugTarget(createExpectedStatementModel(), target);
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the statement example.
    * @return The expected {@link ISEDDebugTarget}.
    */
   public static ISEDDebugTarget createExpectedStatementModel() {
      // Create target
      SEDMemoryDebugTarget target = new SEDMemoryDebugTarget(null);
      target.setModelIdentifier(KeYDebugTarget.MODEL_IDENTIFIER);
      target.setName(STATEMENT_TARGET_NAME);
      // Create thread
      SEDMemoryThread thread = new SEDMemoryThread(target);
      thread.setName(KeYDebugTarget.DEFAULT_THREAD_NAME);
      target.addSymbolicThread(thread);
      // Create statement 1
      SEDMemoryStatement s1 = new SEDMemoryStatement(target, thread, thread);
      s1.setName("int x = 1;");
      s1.setCharEnd(26);
      s1.setCharStart(64);
      s1.setLineNumber(15);
      thread.addChild(s1);
      // Create statement 2
      SEDMemoryStatement s2 = new SEDMemoryStatement(target, s1, thread);
      s2.setName("int y = 2;");
      s2.setCharEnd(26);
      s2.setCharStart(26);
      s2.setLineNumber(16);
      s1.addChild(s2);
      // Create statement 3
      SEDMemoryStatement s3 = new SEDMemoryStatement(target, s2, thread);
      s3.setName("int z = 3;");
      s3.setCharEnd(26);
      s3.setCharStart(26);
      s3.setLineNumber(17);
      s2.addChild(s3);
      return target;
   }

   /**
    * Compares the given {@link ISEDDebugTarget}s with each other.
    * @param expected The expected {@link ISEDDebugTarget}.
    * @param current The current {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */
   public static void compareDebugTarget(ISEDDebugTarget expected, ISEDDebugTarget current) throws DebugException {
      compareDebugTarget(expected, current, true);
   }
   
   /**
    * Compares the given {@link ISEDDebugTarget}s with each other.
    * @param expected The expected {@link ISEDDebugTarget}.
    * @param current The current {@link ISEDDebugTarget}.
    * @param compareReferences Compare also the containment hierarchy?
    * @throws DebugException Occurred Exception.
    */
   public static void compareDebugTarget(ISEDDebugTarget expected, ISEDDebugTarget current, boolean compareReferences) throws DebugException {
      // Compare debug target
      compareDebugTarget((IDebugTarget)expected, (IDebugTarget)current, compareReferences);
      // Compare contained threads
      if (compareReferences) {
         ISEDThread[] expectedThreads = expected.getSymbolicThreads();
         ISEDThread[] currentThreads = current.getSymbolicThreads();
         TestCase.assertEquals(expectedThreads.length, currentThreads.length);
         for (int i = 0; i < expectedThreads.length; i++) {
            compareThread(expectedThreads[i], currentThreads[i], true);
         }
      }
   }
   
   /**
    * Compares the given {@link IDebugTarget}s with each other.
    * @param expected The expected {@link IDebugTarget}.
    * @param current The current {@link IDebugTarget}.
    * @param compareReferences Compare also the containment hierarchy?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareDebugTarget(IDebugTarget expected, IDebugTarget current, boolean compareReferences) throws DebugException {
      // Compare debug target
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), current.getName());
      comparDebugElement(expected, current, false);
      // Compare debug target which should be itself
      TestCase.assertSame(expected, expected.getDebugTarget());
      TestCase.assertSame(current, current.getDebugTarget());
      if (compareReferences) {
         // Compare contained threads
         TestCase.assertEquals(expected.hasThreads(), current.hasThreads());
         IThread[] expectedThreads = expected.getThreads();
         IThread[] currentThreads = current.getThreads();
         TestCase.assertEquals(expectedThreads.length, currentThreads.length);
         for (int i = 0; i < expectedThreads.length; i++) {
            compareThread(expectedThreads[i], currentThreads[i], true);
         }
      }
   }
   
   /**
    * Compares the given {@link ISEDDebugNode}s with each other.
    * @param expected The expected {@link ISEDDebugNode}.
    * @param current The current {@link ISEDDebugNode}.
    * @param compareReferences Compare also the containment hierarchy?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareNode(ISEDDebugNode expected, ISEDDebugNode current, boolean compareReferences) throws DebugException {
      if (expected != null) {
         // Compare node
         TestCase.assertNotNull(current);
         TestCase.assertEquals(expected.getModelIdentifier(), current.getModelIdentifier());
         // Compare parent
         if (compareReferences) {
            compareNode(expected.getParent(), current.getParent(), false);
            // Compare children
            ISEDDebugNode[] expectedChildren = expected.getChildren();
            ISEDDebugNode[] currentChildren = current.getChildren();
            TestCase.assertEquals(expectedChildren.length, currentChildren.length);
            for (int i = 0; i < expectedChildren.length; i++) {
               if (expectedChildren[i] instanceof ISEDBranchCondition) {
                  TestCase.assertTrue(currentChildren[i] instanceof ISEDBranchCondition);
                  compareBranchCondition((ISEDBranchCondition)expectedChildren[i], (ISEDBranchCondition)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDBranchNode) {
                  TestCase.assertTrue(currentChildren[i] instanceof ISEDBranchNode);
                  compareBranchNode((ISEDBranchNode)expectedChildren[i], (ISEDBranchNode)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDExceptionalTermination) {
                  TestCase.assertTrue(currentChildren[i] instanceof ISEDExceptionalTermination);
                  compareExceptionalTermination((ISEDExceptionalTermination)expectedChildren[i], (ISEDExceptionalTermination)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDMethodCall) {
                  TestCase.assertTrue(currentChildren[i] instanceof ISEDMethodCall);
                  compareMethodCall((ISEDMethodCall)expectedChildren[i], (ISEDMethodCall)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDMethodReturn) {
                  TestCase.assertTrue(currentChildren[i] instanceof ISEDMethodReturn);
                  compareMethodReturn((ISEDMethodReturn)expectedChildren[i], (ISEDMethodReturn)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDStatement) {
                  TestCase.assertTrue(currentChildren[i] instanceof ISEDStatement);
                  compareStatement((ISEDStatement)expectedChildren[i], (ISEDStatement)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDTermination) {
                  TestCase.assertTrue(currentChildren[i] instanceof ISEDTermination);
                  compareTermination((ISEDTermination)expectedChildren[i], (ISEDTermination)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDThread) {
                  TestCase.assertTrue(currentChildren[i] instanceof ISEDThread);
                  compareThread((ISEDThread)expectedChildren[i], (ISEDThread)currentChildren[i], true);
               }
               else {
                  TestCase.fail("Unknown node type \"" + (expectedChildren[i] != null ? expectedChildren[i].getClass() : null) + "\".");
               }
            }
         }
      }
      else {
         TestCase.assertNull(current);
      }
   }
   
   /**
    * Compares the given {@link IDebugElement}s with each other.
    * @param expected The expected {@link IDebugElement}.
    * @param current The current {@link IDebugElement}.
    * @param compareReferences Compare also the containment hierarchy?
    * @throws DebugException Occurred Exception.
    */
   protected static void comparDebugElement(IDebugElement expected, IDebugElement current, boolean compareReferences) throws DebugException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getModelIdentifier(), current.getModelIdentifier());
      if (compareReferences) {
         if (expected.getDebugTarget() instanceof ISEDDebugTarget) {
            TestCase.assertTrue(current.getDebugTarget() instanceof ISEDDebugTarget);
            compareDebugTarget((ISEDDebugTarget)expected.getDebugTarget(), (ISEDDebugTarget)current.getDebugTarget(), false);
         }
         else {
            compareDebugTarget(expected.getDebugTarget(), current.getDebugTarget(), false);
         }
      }
   }
   
   /**
    * Compares the given {@link IStackFrame}s with each other.
    * @param expected The expected {@link IStackFrame}.
    * @param current The current {@link IStackFrame}.
    * @throws DebugException Occurred Exception.
    */
   protected static void compareStackFrame(IStackFrame expected, IStackFrame current) throws DebugException {
      if (expected != null) {
         TestCase.assertNotNull(current);
         TestCase.assertEquals(expected.getName(), current.getName());
         TestCase.assertEquals(expected.getName(), expected.getCharEnd(), current.getCharEnd());
         TestCase.assertEquals(expected.getName(), expected.getCharStart(), current.getCharStart());
         TestCase.assertEquals(expected.getName(), expected.getLineNumber(), current.getLineNumber());
         comparDebugElement(expected, current, true);
         if (expected.getThread() instanceof ISEDThread) {
            TestCase.assertTrue(current.getThread() instanceof ISEDThread);
            compareThread((ISEDThread)expected.getThread(), (ISEDThread)current.getThread(), false);
         }
         else {
            compareThread(expected.getThread(), current.getThread(), false);
         }
      }
      else {
         TestCase.assertNull(current);
      }
   }
   
   /**
    * Compares the given {@link IThread}s with each other.
    * @param expected The expected {@link IThread}.
    * @param current The current {@link IThread}.
    * @param compareReferences Compare also the containment hierarchy?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareThread(IThread expected, IThread current, boolean compareReferences) throws DebugException {
      // Compare thread
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), current.getName());
      TestCase.assertEquals(expected.getPriority(), current.getPriority());
      comparDebugElement(expected, current, compareReferences);
      if (compareReferences) {
         // Compare contained stack frames
         TestCase.assertEquals(expected.hasStackFrames(), current.hasStackFrames());
         IStackFrame[] expectedStackFrames = expected.getStackFrames();
         IStackFrame[] currentStackFrames = current.getStackFrames();
         TestCase.assertEquals(expectedStackFrames.length, currentStackFrames.length);
         for (int i = 0; i < expectedStackFrames.length; i++) {
            compareStackFrame(expectedStackFrames[i], currentStackFrames[i]);
         }
         compareStackFrame(expected.getTopStackFrame(), current.getTopStackFrame());
      }
   }
   
   /**
    * Compares the given {@link ISEDThread}s with each other.
    * @param expected The expected {@link ISEDThread}.
    * @param current The current {@link ISEDThread}.
    * @param compareReferences Compare also the containment hierarchy?
    * @throws DebugException Occurred Exception.
    */
   public static void compareThread(ISEDThread expected, ISEDThread current, boolean compareReferences) throws DebugException {
      compareThread((IThread)expected, (IThread)current, compareReferences);
      compareNode(expected, current, compareReferences);
   }

   /**
    * Compares the given {@link ISEDBranchCondition}s with each other.
    * @param expected The expected {@link ISEDBranchCondition}.
    * @param current The current {@link ISEDBranchCondition}.
    * @throws DebugException Occurred Exception.
    */
   public static void compareBranchCondition(ISEDBranchCondition expected, ISEDBranchCondition current) throws DebugException {
      compareStackFrame(expected, current);
      compareNode(expected, current, true);
   }

   /**
    * Compares the given {@link ISEDBranchNode}s with each other.
    * @param expected The expected {@link ISEDBranchNode}.
    * @param current The current {@link ISEDBranchNode}.
    * @throws DebugException Occurred Exception.
    */
   public static void compareBranchNode(ISEDBranchNode expected, ISEDBranchNode current) throws DebugException {
      compareStackFrame(expected, current);
      compareNode(expected, current, true);
   }

   /**
    * Compares the given {@link ISEDMethodCall}s with each other.
    * @param expected The expected {@link ISEDMethodCall}.
    * @param current The current {@link ISEDMethodCall}.
    * @throws DebugException Occurred Exception.
    */
   public static void compareMethodCall(ISEDMethodCall expected, ISEDMethodCall current) throws DebugException {
      compareStackFrame(expected, current);
      compareNode(expected, current, true);
   }

   /**
    * Compares the given {@link ISEDExceptionalTermination}s with each other.
    * @param expected The expected {@link ISEDExceptionalTermination}.
    * @param current The current {@link ISEDExceptionalTermination}.
    * @throws DebugException Occurred Exception.
    */
   public static void compareExceptionalTermination(ISEDExceptionalTermination expected, ISEDExceptionalTermination current) throws DebugException {
      compareTermination(expected, current);
   }

   /**
    * Compares the given {@link ISEDMethodReturn}s with each other.
    * @param expected The expected {@link ISEDMethodReturn}.
    * @param current The current {@link ISEDMethodReturn}.
    * @throws DebugException Occurred Exception.
    */
   public static void compareMethodReturn(ISEDMethodReturn expected, ISEDMethodReturn current) throws DebugException {
      compareStackFrame(expected, current);
      compareNode(expected, current, true);
   }

   /**
    * Compares the given {@link ISEDStatement}s with each other.
    * @param expected The expected {@link ISEDStatement}.
    * @param current The current {@link ISEDStatement}.
    * @throws DebugException Occurred Exception.
    */
   public static void compareStatement(ISEDStatement expected, ISEDStatement current) throws DebugException {
      compareStackFrame(expected, current);
      compareNode(expected, current, true);
   }

   /**
    * Compares the given {@link ISEDTermination}s with each other.
    * @param expected The expected {@link ISEDTermination}.
    * @param current The current {@link ISEDTermination}.
    * @throws DebugException Occurred Exception.
    */
   public static void compareTermination(ISEDTermination expected, ISEDTermination current) throws DebugException {
      compareStackFrame(expected, current);
      compareNode(expected, current, true);
   }
}
