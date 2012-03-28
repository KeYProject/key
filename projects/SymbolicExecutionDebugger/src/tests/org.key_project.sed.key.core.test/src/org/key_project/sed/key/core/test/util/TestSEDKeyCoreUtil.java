package org.key_project.sed.key.core.test.util;

import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
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
import org.key_project.sed.core.model.memory.ISEDMemoryDebugNode;
import org.key_project.sed.core.model.memory.SEDMemoryBranchCondition;
import org.key_project.sed.core.model.memory.SEDMemoryBranchNode;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryMethodCall;
import org.key_project.sed.core.model.memory.SEDMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.core.model.memory.SEDMemoryTermination;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.util.java.ObjectUtil;
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
      SEDMemoryDebugTarget target = appendDebugTarget(targetName);
      appendThread(target);
      return target;
   }
   
   /**
    * Makes sure that the given {@link ISEDDebugTarget} contains the
    * symbolic execution tree of the statement example.
    * @param target The give {@link ISEDDebugTarget} to check.
    * @throws DebugException Occurred Exception.
    */
   public static void assertFlatStepsExample(ISEDDebugTarget target) throws DebugException {
      compareDebugTarget(createExpectedFlatStepsModel(), target);
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the statement example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */
   public static ISEDDebugTarget createExpectedFlatStepsModel() throws DebugException {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(FLAT_STEPS_TARGET_NAME);
      // Create thread
      SEDMemoryThread thread = appendThread(target);
      // Create method call
      SEDMemoryMethodCall call = appendMethodCall(target, thread, thread, "self.doSomething(_asdf,_a,_b);", 228, 239);
      // Create statement 1
      SEDMemoryStatement s1 = appendStatement(target, call, thread, "int x = 1;", 276, 286);
      // Create statement 2
      SEDMemoryStatement s2 = appendStatement(target, s1, thread, "int y = 2;", 290, 300);
      // Create statement 3
      SEDMemoryStatement s3 = appendStatement(target, s2, thread, "int z = 3;", 304, 314);
      // Create method return
      SEDMemoryMethodReturn ret = appendMethodReturn(target, s3, thread, "self.doSomething(_asdf,_a,_b);", call);
      // Create termination
      appendTermination(target, ret);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the method call format test example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */   
   public static ISEDDebugTarget createExpectedMethodCallFormatTestModel() throws DebugException {
      SEDMemoryDebugTarget target = appendDebugTarget(METHOD_CALL_FORMAT_TEST_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "MethodFormatTest.main();", 54, 58);
      SEDMemoryStatement sMain = appendStatement(target, callMain, thread, "return a();", 62, 73);
      
      SEDMemoryMethodCall callA = appendMethodCall(target, sMain, thread, "MethodFormatTest.a();", 100, 101);
      SEDMemoryStatement sA = appendStatement(target, callA, thread, "return b();", 105, 116);
      
      SEDMemoryMethodCall callB = appendMethodCall(target, sA, thread, "MethodFormatTest.b();", 136, 137);
      SEDMemoryStatement sB = appendStatement(target, callB, thread, "return c();", 142, 153);
      
      SEDMemoryMethodCall callC = appendMethodCall(target, sB, thread, "MethodFormatTest.c();", 173, 174);
      SEDMemoryStatement sC = appendStatement(target, callC, thread, "return d();", 178, 189);
      
      SEDMemoryMethodCall callD = appendMethodCall(target, sC, thread, "MethodFormatTest.d();", 214, 215);
      SEDMemoryStatement sD = appendStatement(target, callD, thread, "return e();", 219, 230);
      
      SEDMemoryMethodCall callE = appendMethodCall(target, sD, thread, "MethodFormatTest.e();", 252, 253);
      SEDMemoryStatement sE = appendStatement(target, callE, thread, "return f();", 257, 268);
      
      SEDMemoryMethodCall callF = appendMethodCall(target, sE, thread, "MethodFormatTest.f();", 294, 295);
      SEDMemoryStatement sF = appendStatement(target, callF, thread, "return g();", 299, 310);
      
      SEDMemoryMethodCall callG = appendMethodCall(target, sF, thread, "MethodFormatTest.g();", 332, 333);
      SEDMemoryStatement sG = appendStatement(target, callG, thread, "return 42;", 341, 351);
      
      SEDMemoryMethodReturn retG = appendMethodReturn(target, sG, thread, "MethodFormatTest.g();", callG);
      SEDMemoryMethodReturn retF = appendMethodReturn(target, retG, thread, "MethodFormatTest.f();", callF);
      SEDMemoryMethodReturn retE = appendMethodReturn(target, retF, thread, "MethodFormatTest.e();", callE);
      SEDMemoryMethodReturn retD = appendMethodReturn(target, retE, thread, "MethodFormatTest.d();", callD);
      SEDMemoryMethodReturn retC = appendMethodReturn(target, retD, thread, "MethodFormatTest.c();", callC);
      SEDMemoryMethodReturn retB = appendMethodReturn(target, retC, thread, "MethodFormatTest.b();", callB);
      SEDMemoryMethodReturn retA = appendMethodReturn(target, retB, thread, "MethodFormatTest.a();", callA);
      SEDMemoryMethodReturn retMain = appendMethodReturn(target, retA, thread, "MethodFormatTest.main();", callMain);
      appendTermination(target, retMain);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the fixed recursive method call example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */   
   public static ISEDDebugTarget createExpectedFixedRecursiveMethodCallModel() throws DebugException {
      SEDMemoryDebugTarget target = appendDebugTarget(FIXED_RECURSIVE_METHOD_CALL_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "FixedRecursiveMethodCallTest.decreaseValue();", 66, 79);
      SEDMemoryStatement sMain = appendStatement(target, callMain, thread, "return decrease(3);", 87, 106);
      
      SEDMemoryMethodCall call1 = appendMethodCall(target, sMain, thread, "FixedRecursiveMethodCallTest.decrease(n);", 134, 142);
      SEDMemoryBranchNode branch1 = appendBranchNode(target, call1, thread, "if (n>=1) {return decrease(n-1); }", 155, 201);
      SEDMemoryStatement s1 = appendStatement(target, branch1, thread, "return decrease(n-1);", 173, 196);
      
      SEDMemoryMethodCall call2 = appendMethodCall(target, s1, thread, "FixedRecursiveMethodCallTest.decrease(n_1);", 134, 142);
      SEDMemoryBranchNode branch2 = appendBranchNode(target, call2, thread, "if (n_1>=1) {return decrease(n_1-1); }", 155, 201);
      SEDMemoryStatement s2 = appendStatement(target, branch2, thread, "return decrease(n_1-1);", 173, 196);

      SEDMemoryMethodCall call3 = appendMethodCall(target, s2, thread, "FixedRecursiveMethodCallTest.decrease(n_2);", 134, 142);
      SEDMemoryBranchNode branch3 = appendBranchNode(target, call3, thread, "if (n_2>=1) {return decrease(n_2-1); }", 155, 201);
      SEDMemoryStatement s3 = appendStatement(target, branch3, thread, "return decrease(n_2-1);", 173, 196);

      SEDMemoryMethodCall call4 = appendMethodCall(target, s3, thread, "FixedRecursiveMethodCallTest.decrease(n_3);", 134, 142);
      SEDMemoryBranchNode branch4 = appendBranchNode(target, call4, thread, "if (n_3>=1) {return decrease(n_3-1); }", 155, 201);
      SEDMemoryStatement s4 = appendStatement(target, branch4, thread, "return n_3;", 205, 214);
      
      SEDMemoryMethodReturn ret4 = appendMethodReturn(target, s4, thread, "FixedRecursiveMethodCallTest.decrease(n_3);", call4);
      SEDMemoryMethodReturn ret3 = appendMethodReturn(target, ret4, thread, "FixedRecursiveMethodCallTest.decrease(n_2);", call3);
      SEDMemoryMethodReturn ret2 = appendMethodReturn(target, ret3, thread, "FixedRecursiveMethodCallTest.decrease(n_1);", call2);
      SEDMemoryMethodReturn ret1 = appendMethodReturn(target, ret2, thread, "FixedRecursiveMethodCallTest.decrease(n);", call1);
      SEDMemoryMethodReturn ret = appendMethodReturn(target, ret1, thread, "FixedRecursiveMethodCallTest.decreaseValue();", callMain);
      appendTermination(target, ret);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the else if different variables example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */   
   public static ISEDDebugTarget createExpectedElseIfDifferentVariablesModel() throws DebugException {
      SEDMemoryDebugTarget target = appendDebugTarget(ELSE_IF_DIFFERENT_VARIABLES_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall call = appendMethodCall(target, thread, thread, "self.main(_a,_b);", 55, 59);
      
      SEDMemoryBranchNode bn1 = appendBranchNode(target, call, thread, "if (_a) {return 1; }else if (_b) {return 2;   }else  {return 3;   }", 87, 179);
      
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, bn1, "if _a true");
      SEDMemoryStatement s1 = appendStatement(target, bc1, thread, "return 1;", 100, 109);
      SEDMemoryMethodReturn ret1 = appendMethodReturn(target, s1, thread, "self.main(_a,_b);", call);
      appendTermination(target, ret1);

      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, bn1, "if _a false");
      SEDMemoryBranchNode bn2 = appendBranchNode(target, bc2, thread, "if (_b) {return 2; }else  {return 3; }", 87, 179);
      SEDMemoryBranchCondition bc2a = appendBranchCondition(target, bn2, "b = TRUE TRUE");
      SEDMemoryStatement s2 = appendStatement(target, bc2a, thread, "return 2;", 136, 145);
      SEDMemoryMethodReturn ret2 = appendMethodReturn(target, s2, thread, "self.main(_a,_b);", call);
      appendTermination(target, ret2);

      SEDMemoryBranchCondition bc2b = appendBranchCondition(target, bn2, "b = TRUE FALSE");
      SEDMemoryStatement s3 = appendStatement(target, bc2b, thread, "return 3;", 165, 174);
      SEDMemoryMethodReturn ret3 = appendMethodReturn(target, s3, thread, "self.main(_a,_b);", call);
      appendTermination(target, ret3);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the try catch finally example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */
   public static ISEDDebugTarget createExpectedTryCatchFinallyModel() throws DebugException {
      SEDMemoryDebugTarget target = appendDebugTarget(TRY_CATCH_FINALLY_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall call = appendMethodCall(target, thread, thread, "self.tryCatchFinally(_input);", 97, 112);
      SEDMemoryStatement s1 = appendStatement(target, call, thread, "int result = 0;", 129, 144);
      SEDMemoryStatement s2 = appendStatement(target, s1, thread, "result_1=1/_input;", 158, 177);
      
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, s2, "input = 0 TRUE");
      SEDMemoryBranchCondition bc1a = appendBranchCondition(target, bc1, "Normal Execution (a_1 != null)");
      SEDMemoryBranchCondition bc1b = appendBranchCondition(target, bc1a, "if a instanceof ArithmeticException true");
      SEDMemoryBranchCondition bc1c = appendBranchCondition(target, bc1b, "Normal Execution (a instanceof ArithmeticException)");
      SEDMemoryStatement bc1S1 = appendStatement(target, bc1c, thread, "result_1=2;", 222, 233);
      SEDMemoryStatement bc1S2 = appendStatement(target, bc1S1, thread, "result_1=result_1*2;", 256, 276);
      SEDMemoryStatement bc1S3 = appendStatement(target, bc1S2, thread, "return result_1;", 285, 299);
      SEDMemoryMethodReturn bc1ret = appendMethodReturn(target, bc1S3, thread, "self.tryCatchFinally(_input);", call);
      appendTermination(target, bc1ret);
      
      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, s2, "input = 0 FALSE");
      SEDMemoryStatement bc2S1 = appendStatement(target, bc2, thread, "result_1=result_1*2;", 256, 276);
      SEDMemoryStatement bc2S2 = appendStatement(target, bc2S1, thread, "return result_1;", 285, 299);
      SEDMemoryMethodReturn bc2ret = appendMethodReturn(target, bc2S2, thread, "self.tryCatchFinally(_input);", call);
      appendTermination(target, bc2ret);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the static method call example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */
   public static ISEDDebugTarget createExpectedStaticMethodCallModel() throws DebugException {
      SEDMemoryDebugTarget target = appendDebugTarget(STATIC_METHOD_CALL_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall mainCall = appendMethodCall(target, thread, thread, "StaticMethodCall.main();", 662, 666);
      SEDMemoryStatement mainS1 = appendStatement(target, mainCall, thread, "doSomething();", 674, 688);
      SEDMemoryMethodCall doSomethingCall = appendMethodCall(target, mainS1, thread, "StaticMethodCall.doSomething();", 756, 767);
      SEDMemoryMethodReturn doSomethingReturn = appendMethodReturn(target, doSomethingCall, thread, "StaticMethodCall.doSomething();", doSomethingCall);
      SEDMemoryStatement mainS2 = appendStatement(target, doSomethingReturn, thread, "int x = sub()+sub();",  692, 714);
      
      SEDMemoryMethodCall subCall1 = appendMethodCall(target, mainS2, thread, "StaticMethodCall.sub();", 799, 802);
      SEDMemoryStatement subCall1S = appendStatement(target, subCall1, thread, "return subSub()+2;", 810, 830);
      SEDMemoryMethodCall subSubCall1 = appendMethodCall(target, subCall1S, thread, "StaticMethodCall.subSub();", 858, 864);
      SEDMemoryStatement subSubCall1S = appendStatement(target, subSubCall1, thread, "return 2;", 872, 881);
      SEDMemoryMethodReturn subSubReturn1 = appendMethodReturn(target, subSubCall1S, thread, "StaticMethodCall.subSub();", subSubCall1);
      SEDMemoryMethodReturn subReturn1 = appendMethodReturn(target, subSubReturn1, thread, "StaticMethodCall.sub();", subCall1);

      SEDMemoryMethodCall subCall2 = appendMethodCall(target, subReturn1, thread, "StaticMethodCall.sub();", 799, 802);
      SEDMemoryStatement subCall2S = appendStatement(target, subCall2, thread, "return subSub()+2;", 810, 830);
      SEDMemoryMethodCall subSubCall2 = appendMethodCall(target, subCall2S, thread, "StaticMethodCall.subSub();", 858, 864);
      SEDMemoryStatement subSubCall2S = appendStatement(target, subSubCall2, thread, "return 2;", 872, 881);
      SEDMemoryMethodReturn subSubReturn2 = appendMethodReturn(target, subSubCall2S, thread, "StaticMethodCall.subSub();", subSubCall2);
      SEDMemoryMethodReturn subReturn2 = appendMethodReturn(target, subSubReturn2, thread, "StaticMethodCall.sub();", subCall2);
      
      SEDMemoryStatement mainS3 = appendStatement(target, subReturn2, thread, "return x;", 718, 727);
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, mainS3, thread, "StaticMethodCall.main();", mainCall);
      appendTermination(target, mainReturn);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the complex flat steps example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */   
   public static ISEDDebugTarget createExpectedComplexFlatStepsModel() throws DebugException {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(COMPLEX_FLAT_STEPS_TARGET_NAME);
      // Create thread
      SEDMemoryThread thread = appendThread(target);
      // Create method call
      SEDMemoryMethodCall call = appendMethodCall(target, thread, thread, "self.doSomething();", 244, 255);
      // Create statement 1
      SEDMemoryStatement s1 = appendStatement(target, call, thread, "int x = 1+2;", 263, 277);
      // Create statement 2
      SEDMemoryStatement s2 = appendStatement(target, s1, thread, "int y = 2*4*9;", 281, 299);
      // Create statement 3
      SEDMemoryStatement s3 = appendStatement(target, s2, thread, "int z = 3*(4/(2-3));", 303, 329);
      // Create method return
      SEDMemoryMethodReturn ret = appendMethodReturn(target, s3, thread, "self.doSomething();", call);
      // Create termination
      appendTermination(target, ret);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the method call on object example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */
   public static ISEDDebugTarget createExpectedMethodCallOnObjectModel() throws DebugException {
      SEDMemoryDebugTarget target = appendDebugTarget(METHOD_CALL_ON_OBJECT_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "MethodCallOnObject.main();", 56, 60);
      SEDMemoryStatement mainS1 = appendStatement(target, callMain, thread, "MethodCallOnObject x = new MethodCallOnObject ();", 68, 116);
      SEDMemoryBranchCondition b1 = appendBranchCondition(target, mainS1, "Normal Execution (m != null)");
      SEDMemoryStatement mainS2 = appendStatement(target, b1, thread, "return x.doSomething();", 120, 143);
      SEDMemoryBranchCondition b2 = appendBranchCondition(target, mainS2, "Normal Execution (x != null)");
      SEDMemoryMethodCall callDo = appendMethodCall(target, b2, thread, "x.doSomething();", 164, 175);
      SEDMemoryStatement doS = appendStatement(target, callDo, thread, "return 42;", 183, 193);
      SEDMemoryMethodReturn doReturn = appendMethodReturn(target, doS, thread, "x.doSomething();", callDo);
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, doReturn, thread, "MethodCallOnObject.main();", callMain);
      appendTermination(target, mainReturn);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the method call on object with exception example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */   
   public static ISEDDebugTarget createExpectedMethodCallOnObjectWithExceptionModel() throws DebugException {
      SEDMemoryDebugTarget target = appendDebugTarget(METHOD_CALL_ON_OBJECT_WITH_EXCEPTION_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "MethodCallOnObjectWithException.main();", 69, 73);
      SEDMemoryStatement mainS1 = appendStatement(target, callMain, thread, "MethodCallOnObjectWithException x = new MethodCallOnObjectWithException ();", 91, 165);
      SEDMemoryBranchCondition b1 = appendBranchCondition(target, mainS1, "Normal Execution (m != null)");
      SEDMemoryStatement mainS2 = appendStatement(target, b1, thread, "return x.doSomething();", 170, 193);
      SEDMemoryBranchCondition b2 = appendBranchCondition(target, mainS2, "Normal Execution (x != null)");
      SEDMemoryMethodCall callDo = appendMethodCall(target, b2, thread, "x.doSomething();", 364, 375);
      SEDMemoryStatement doS1 = appendStatement(target, callDo, thread, "MethodCallOnObjectWithException x = null;", 383, 424);
      SEDMemoryStatement doS2 = appendStatement(target, doS1, thread, "return x_3.return42();", 428, 448);
      SEDMemoryBranchCondition b3 = appendBranchCondition(target, doS2, "Null Reference (x_3 = null)");
      SEDMemoryBranchCondition b4 = appendBranchCondition(target, b3, "Normal Execution (n_1 != null)");
//      SEDMemoryBranchCondition b5 = appendBranchCondition(target, b4, thread, "if n instanceof NullPointerException true");
      SEDMemoryBranchCondition b6 = appendBranchCondition(target, b4, "Normal Execution (n instanceof NullPointerException)");
      SEDMemoryStatement mainS3 = appendStatement(target, b6, thread, "MethodCallOnObjectWithException y = new MethodCallOnObjectWithException ();", 239, 313);
      SEDMemoryBranchCondition b7 = appendBranchCondition(target, mainS3, "Normal Execution (m_3 != null)");
      SEDMemoryStatement mainS4 = appendStatement(target, b7, thread, "return y.return42();", 318, 338);
      SEDMemoryBranchCondition b8 = appendBranchCondition(target, mainS4, "Normal Execution (y != null)");
      SEDMemoryMethodCall call42 = appendMethodCall(target, b8, thread, "y.return42();", 469, 477);
      SEDMemoryStatement return42S = appendStatement(target, call42, thread, "return 42;", 485, 495);
      SEDMemoryMethodReturn call42Return = appendMethodReturn(target, return42S, thread, "y.return42();", call42);
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, call42Return, thread, "MethodCallOnObjectWithException.main();", callMain);
      appendTermination(target, mainReturn);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the method call parallel example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */
   public static ISEDDebugTarget createExpectedMethodCallParallelModel() throws DebugException {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(METHOD_CALL_PARALLEL_TARGET_NAME);
      // Create thread
      SEDMemoryThread thread = appendThread(target);
      // Create method call main
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "self.main();", 53, 57);
      // Create statement a()
      SEDMemoryStatement mainStatement1 = appendStatement(target, callMain, thread, "int a = a();", 65, 77); 
      // Create method call a
      SEDMemoryMethodCall callA = appendMethodCall(target, mainStatement1, thread, "self.a();", 131, 132);
      // Create statement b()
      SEDMemoryStatement aStatement1 = appendStatement(target, callA, thread, "int b1 = b();", 140, 153); 
      // Create method call b
      SEDMemoryMethodCall callB = appendMethodCall(target, aStatement1, thread, "self.b();", 230, 231);
      // Create statement c()
      SEDMemoryStatement bStatement = appendStatement(target, callB, thread, "return c();", 239, 250); 
      // Create method call c
      SEDMemoryMethodCall callC = appendMethodCall(target, bStatement, thread, "self.c();", 271, 272);
      // Create statement 42
      SEDMemoryStatement fourtyTwoStatement = appendStatement(target, callC, thread, "return 42;", 280, 290); 
      // Create method return of c
      SEDMemoryMethodReturn cReturn = appendMethodReturn(target, fourtyTwoStatement, thread, "self.c();", callC);
      // Create method return of b
      SEDMemoryMethodReturn bReturn = appendMethodReturn(target, cReturn, thread, "self.b();", callB); 
      // Create statement b()
      SEDMemoryStatement aStatement2 = appendStatement(target, bReturn, thread, "int b2 = b();", 157, 170); 
      // Create method call b
      SEDMemoryMethodCall callB2 = appendMethodCall(target, aStatement2, thread, "self.b();", 230, 231); ;
      // Create statement c()
      SEDMemoryStatement bStatement2 = appendStatement(target, callB2, thread, "return c();", 239, 250);
      // Create method call c
      SEDMemoryMethodCall callC2 = appendMethodCall(target, bStatement2, thread, "self.c();", 271, 272); 
      // Create statement 42
      SEDMemoryStatement fourtyTwoStatement2 = appendStatement(target, callC2, thread, "return 42;", 280, 290); 
      // Create method return of c
      SEDMemoryMethodReturn cReturn2 = appendMethodReturn(target, fourtyTwoStatement2, thread, "self.c();", callC2); 
      // Create method return of b
      SEDMemoryMethodReturn bReturn2 = appendMethodReturn(target, cReturn2, thread, "self.b();", callB2); 
      // Create statement c()
      SEDMemoryStatement aStatement3 = appendStatement(target, bReturn2, thread, "int c = c();", 174, 186); 
      // Create method call c
      SEDMemoryMethodCall callC3 = appendMethodCall(target, aStatement3, thread, "self.c();", 271, 272);
      // Create statement 42
      SEDMemoryStatement fourtyTwoStatement3 = appendStatement(target, callC3, thread, "return 42;", 280, 290); 
      // Create method return of c
      SEDMemoryMethodReturn cReturn3 = appendMethodReturn(target, fourtyTwoStatement3, thread, "self.c();", callC3); 
      // Create statement return
      SEDMemoryStatement aStatement4 = appendStatement(target, cReturn3, thread, "return b1+b2+c;", 190, 209); 
      // Create method return of a
      SEDMemoryMethodReturn aReturn = appendMethodReturn(target, aStatement4, thread, "self.a();", callA); 
      // Create statement x()
      SEDMemoryStatement mainStatement2 = appendStatement(target, aReturn, thread, "int x = x();", 81, 93); 
      // Create method call x
      SEDMemoryMethodCall callX = appendMethodCall(target, mainStatement2, thread, "self.x();", 311, 312);
      // Create statement 42
      SEDMemoryStatement twoStatement = appendStatement(target, callX, thread, "return 2;", 320, 329);
      // Create method return of c
      SEDMemoryMethodReturn xReturn = appendMethodReturn(target, twoStatement, thread, "self.x();", callX); 
      // Create statement return
      SEDMemoryStatement mainStatement3 = appendStatement(target, xReturn, thread, "return a*x;", 97, 110);
      // Create method return
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, mainStatement3, thread, "self.main();", callMain);
      // Create termination
      appendTermination(target, mainReturn);
      return target;
   }
   
   /**
    * Creates the expected {@link ISEDDebugTarget} for the simple if example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */
   public static ISEDDebugTarget createExpectedSimpleIfModel() throws DebugException {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(SIMPLE_IF_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall callMin = appendMethodCall(target, thread, thread, "self.min(_i,_j);", 413, 416);
      SEDMemoryStatement s1 = appendStatement(target, callMin, thread, "int result;", 436, 447);
      SEDMemoryBranchNode branchNode = appendBranchNode(target, s1, thread, "if (_i<_j) {   result_1=_i; }else  {   result_1=_j; }", 451, 515);
      // Branch 1
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, branchNode, "j >= 1 + i TRUE");
      SEDMemoryStatement s2 = appendStatement(target, bc1, thread, "result_1=_i;", 468, 479);
      SEDMemoryStatement s3 = appendStatement(target, s2, thread, "return result_1;", 519, 533);
      SEDMemoryMethodReturn minReturn1 = appendMethodReturn(target, s3, thread, "self.min(_i,_j);", callMin);
      appendTermination(target, minReturn1);
      // Branch 2
      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, branchNode, "j >= 1 + i FALSE");
      SEDMemoryStatement s4 = appendStatement(target, bc2, thread, "result_1=_j;", 499, 510);
      SEDMemoryStatement s5 = appendStatement(target, s4, thread, "return result_1;", 519, 533);
      SEDMemoryMethodReturn minReturn2 = appendMethodReturn(target, s5, thread, "self.min(_i,_j);", callMin);
      appendTermination(target, minReturn2);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the functional if example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */
   public static ISEDDebugTarget createExpectedFunctionalIfModel() throws DebugException {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(FUNCTIONAL_IF_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall callMin = appendMethodCall(target, thread, thread, "self.min(_i,_j);", 661, 664);
      SEDMemoryStatement s1 = appendStatement(target, callMin, thread, "int result;", 684, 695);
      SEDMemoryBranchNode branchNode = appendBranchNode(target, s1, thread, "if (invert(_i)<invert(_j)) {   result_1=_i; }else  {   result_1=_j; }", 699, 779);
      SEDMemoryMethodCall callInvert1 = appendMethodCall(target, branchNode, thread, "self.invert(a);", 818, 824);
      SEDMemoryStatement callS1 = appendStatement(target, callInvert1, thread, "return a*-1;", 837, 851);
      SEDMemoryMethodReturn returnInvert1 = appendMethodReturn(target, callS1, thread, "self.invert(a);", callInvert1);
      SEDMemoryMethodCall callInvert2 = appendMethodCall(target, returnInvert1, thread, "self.invert(a_1);", 818, 824);
      SEDMemoryStatement callS2 = appendStatement(target, callInvert2, thread, "return a_1*-1;", 837, 851);
      SEDMemoryMethodReturn returnInvert2 = appendMethodReturn(target, callS2, thread, "self.invert(a_1);", callInvert2);
      // Branch 1
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, returnInvert2, "j <= -1 + i TRUE");
      SEDMemoryStatement s2 = appendStatement(target, bc1, thread, "result_1=_i;", 732, 743);
      SEDMemoryStatement s3 = appendStatement(target, s2, thread, "return result_1;", 783, 797);
      SEDMemoryMethodReturn minReturn1 = appendMethodReturn(target, s3, thread, "self.min(_i,_j);", callMin);
      appendTermination(target, minReturn1);
      // Branch 2
      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, returnInvert2, "j <= -1 + i FALSE");
      SEDMemoryStatement s4 = appendStatement(target, bc2, thread, "result_1=_j;", 763, 774);
      SEDMemoryStatement s5 = appendStatement(target, s4, thread, "return result_1;", 783, 797);
      SEDMemoryMethodReturn minReturn2 = appendMethodReturn(target, s5, thread, "self.min(_i,_j);", callMin);
      appendTermination(target, minReturn2);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the complex if example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */   
   public static ISEDDebugTarget createExpectedComplexIfModel() throws DebugException {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(COMPLEX_IF_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall callMin = appendMethodCall(target, thread, thread, "self.min(_i,_j);", 424, 427);
      SEDMemoryStatement s1 = appendStatement(target, callMin, thread, "int result;", 447, 458);
      SEDMemoryBranchNode branchNode = appendBranchNode(target, s1, thread, "if (_i<_j&&_i!=_j) {   result_1=_i; }else  {   result_1=_j; }", 462, 536);
      // Branch 1
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, branchNode, "j >= 1 + i TRUE");
      SEDMemoryBranchCondition bc1a = appendBranchCondition(target, bc1, "if x_2 true");
      SEDMemoryStatement s2 = appendStatement(target, bc1a, thread, "result_1=_i;", 489, 500);
      SEDMemoryStatement s3 = appendStatement(target, s2, thread, "return result_1;", 540, 554);
      SEDMemoryMethodReturn minReturn1 = appendMethodReturn(target, s3, thread, "self.min(_i,_j);", callMin);
      appendTermination(target, minReturn1);
      // Branch 2
      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, branchNode, "j >= 1 + i FALSE");
      SEDMemoryStatement s4 = appendStatement(target, bc2, thread, "result_1=_j;", 520, 531);
      SEDMemoryStatement s5 = appendStatement(target, s4, thread, "return result_1;", 540, 554);
      SEDMemoryMethodReturn minReturn2 = appendMethodReturn(target, s5, thread, "self.min(_i,_j);", callMin);
      appendTermination(target, minReturn2);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the method call hierarchy example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */
   public static ISEDDebugTarget createExpectedMethodCallHierarchyModel() throws DebugException {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(METHOD_CALL_HIERARCHY_TARGET_NAME);
      // Create thread
      SEDMemoryThread thread = appendThread(target);
      // Create method call main
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "self.main();", 54, 58);
      // Create statement a()
      SEDMemoryStatement mainStatement = appendStatement(target, callMain, thread, "return a();", 66, 77);
      // Create method call a
      SEDMemoryMethodCall callA = appendMethodCall(target, mainStatement, thread, "self.a();", 98, 99);
      // Create statement b()
      SEDMemoryStatement aStatement = appendStatement(target, callA, thread, "return b();", 107, 118);
      // Create method call b
      SEDMemoryMethodCall callB = appendMethodCall(target, aStatement, thread, "self.b();", 139, 140);
      // Create statement c()
      SEDMemoryStatement bStatement = appendStatement(target, callB, thread, "return c();", 148, 159);
      // Create method call c
      SEDMemoryMethodCall callC = appendMethodCall(target, bStatement, thread, "self.c();", 180, 181);
      // Create statement 42
      SEDMemoryStatement fourtyTwoStatement = appendStatement(target, callC, thread, "return 42;", 189, 199);
      // Create method return of c
      SEDMemoryMethodReturn cReturn = appendMethodReturn(target, fourtyTwoStatement, thread, "self.c();", callC);
      // Create method return of b
      SEDMemoryMethodReturn bReturn = appendMethodReturn(target, cReturn, thread, "self.b();", callB);
      // Create method return of a
      SEDMemoryMethodReturn aReturn = appendMethodReturn(target, bReturn, thread, "self.a();", callA);
      // Create method return
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, aReturn, thread, "self.main();", callMain);
      // Create termination
      appendTermination(target, mainReturn);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the method call hierarchy with exception example.
    * @return The expected {@link ISEDDebugTarget}.
    * @throws DebugException Occurred Exception.
    */   
   public static ISEDDebugTarget createExpectedMethodCallHierarchyWithExceptionModel() throws DebugException {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(METHOD_CALL_HIERARCHY_WITH_EXCEPTION_TARGET_NAME);
      // Create thread
      SEDMemoryThread thread = appendThread(target);
      // Create method call main
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "self.main();", 125, 129);
      // Create statement a()
      SEDMemoryStatement mainStatement = appendStatement(target, callMain, thread, "a();", 141, 145);
      // Create method call a
      SEDMemoryMethodCall callA = appendMethodCall(target, mainStatement, thread, "self.a();", 173, 174);
      // Create statement b()
      SEDMemoryStatement aStatement = appendStatement(target, callA, thread, "b();", 202, 206);
      // Create method call b
      SEDMemoryMethodCall callB = appendMethodCall(target, aStatement, thread, "self.b();", 330, 331);
      // Create statement c()
      SEDMemoryStatement bStatement = appendStatement(target, callB, thread, "c();", 343, 347);
      // Create method call c
      SEDMemoryMethodCall callC = appendMethodCall(target, bStatement, thread, "self.c();", 375, 376);
      // Create statement 42
      SEDMemoryStatement throwStatement = appendStatement(target, callC, thread, "throw new RuntimeException ();", 388, 417);
      // Create branch condition 1
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, throwStatement, "Normal Execution (r_1 != null)");
      // Create branch condition 2
      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, bc1, "Normal Execution (r instanceof RuntimeException)");
      // Create statement ae assignment
      SEDMemoryStatement aeAssignmentStatement = appendStatement(target, bc2, thread, "int ae = -1;", 262, 274);
      // Create statement a assignment
      SEDMemoryStatement aAssignmentStatement = appendStatement(target, aeAssignmentStatement, thread, "int a1 = 1;", 291, 302);
      // Create method return of a
      SEDMemoryMethodReturn aReturn = appendMethodReturn(target, aAssignmentStatement, thread, "self.a();", callA);
      // Create method return
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, aReturn, thread, "self.main();", callMain);
      // Create termination
      appendTermination(target, mainReturn);
      return target;
   }
   
   /**
    * Appends a new debug target to a not existing {@link ILaunch}.
    * @param name The name to use.
    * @return The created {@link SEDMemoryDebugTarget}.
    */
   public static SEDMemoryDebugTarget appendDebugTarget(String name) {
      SEDMemoryDebugTarget target = new SEDMemoryDebugTarget(null);
      target.setModelIdentifier(KeYDebugTarget.MODEL_IDENTIFIER);
      target.setName(name);
      return target;
   }
   
   /**
    * Appends a new thread to the given {@link SEDMemoryDebugTarget}.
    * @param target The {@link SEDMemoryDebugTarget} to append to.
    * @return The created {@link SEDMemoryThread}.
    */
   public static SEDMemoryThread appendThread(SEDMemoryDebugTarget target) {
      SEDMemoryThread thread = new SEDMemoryThread(target);
      thread.setName(KeYDebugTarget.DEFAULT_THREAD_NAME);
      target.addSymbolicThread(thread);
      return thread;
   }
   
   /**
    * Appends a new method call to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @param thread The {@link ISEDThread} to use.
    * @param name The name to set on the created {@link SEDMemoryMethodCall}.
    * @param charStart The index of the start character to set on the created {@link SEDMemoryMethodCall}
    * @param charEnd The index of the end character to set on the created {@link SEDMemoryMethodCall}
    * @return The created {@link SEDMemoryMethodCall}.
    */
   public static SEDMemoryMethodCall appendMethodCall(ISEDDebugTarget target, 
                                                      ISEDMemoryDebugNode parent, 
                                                      ISEDThread thread,
                                                      String name,
                                                      int charStart,
                                                      int charEnd) {
      SEDMemoryMethodCall methodCall = new SEDMemoryMethodCall(target, parent, thread);
      methodCall.setName(name);
      methodCall.setCharStart(charStart);
      methodCall.setCharEnd(charEnd);
      parent.addChild(methodCall);
      return methodCall;
   }
   
   /**
    * Appends a new statement to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @param thread The {@link ISEDThread} to use.
    * @param name The name to set on the created {@link SEDMemoryStatement}.
    * @param charStart The index of the start character to set on the created {@link SEDMemoryStatement}
    * @param charEnd The index of the end character to set on the created {@link SEDMemoryStatement}
    * @return The created {@link SEDMemoryStatement}.
    */
   public static SEDMemoryStatement appendStatement(ISEDDebugTarget target, 
                                                    ISEDMemoryDebugNode parent, 
                                                    ISEDThread thread,
                                                    String name,
                                                    int charStart,
                                                    int charEnd) {
      SEDMemoryStatement statement = new SEDMemoryStatement(target, parent, thread);
      statement.setName(name);
      statement.setCharStart(charStart);
      statement.setCharEnd(charEnd);
      parent.addChild(statement);
      return statement;
   }
   
   /**
    * Appends a new method return to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @param thread The {@link ISEDThread} to use.
    * @param name The name to set on the created {@link SEDMemoryMethodReturn}.
    * @param lineNumber The line number to set on the created {@link SEDMemoryMethodReturn}.
    * @return The created {@link SEDMemoryMethodReturn}.
    * @throws DebugException Occurred Exception
    */
   public static SEDMemoryMethodReturn appendMethodReturn(ISEDDebugTarget target, 
                                                          ISEDMemoryDebugNode parent, 
                                                          ISEDThread thread,
                                                          String name,
                                                          ISEDMethodCall callNode) throws DebugException {
      SEDMemoryMethodReturn methodReturn = new SEDMemoryMethodReturn(target, parent, thread);
      methodReturn.setName(KeYDebugTarget.createMethodReturnName(null, name));
      methodReturn.setLineNumber(callNode.getLineNumber());
      methodReturn.setCharStart(callNode.getCharStart());
      methodReturn.setCharEnd(callNode.getCharEnd());
      parent.addChild(methodReturn);
      return methodReturn;
   }
   
   /**
    * Appends a new termination to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @return The created {@link SEDMemoryTermination}.
    */
   public static SEDMemoryTermination appendTermination(ISEDDebugTarget target, 
                                                        ISEDMemoryDebugNode parent) {
      SEDMemoryTermination termination = new SEDMemoryTermination(target, parent);
      termination.setName(KeYDebugTarget.DEFAULT_TERMINATION_NODE_NAME);
      parent.addChild(termination);
      return termination;
   }
   
   /**
    * Appends a new branch node to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @param thread The {@link ISEDThread} to use.
    * @param name The name to set on the created {@link SEDMemoryBranchNode}.
    * @param charStart The index of the start character to set on the created {@link SEDMemoryBranchNode}
    * @param charEnd The index of the end character to set on the created {@link SEDMemoryBranchNode}
    * @return The created {@link SEDMemoryBranchNode}.
    */
   public static SEDMemoryBranchNode appendBranchNode(ISEDDebugTarget target, 
                                                      ISEDMemoryDebugNode parent, 
                                                      ISEDThread thread,
                                                      String name,
                                                      int charStart,
                                                      int charEnd) {
      SEDMemoryBranchNode bn = new SEDMemoryBranchNode(target, parent, thread);
      bn.setName(name);
      bn.setCharStart(charStart);
      bn.setCharEnd(charEnd);
      parent.addChild(bn);
      return bn;
   }
   
   /**
    * Appends a new branch condition to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @param name The name to set on the created {@link SEDMemoryBranchCondition}.
    * @return The created {@link SEDMemoryBranchCondition}.
    */
   public static SEDMemoryBranchCondition appendBranchCondition(ISEDDebugTarget target, 
                                                                ISEDMemoryDebugNode parent, 
                                                                String name) {
      SEDMemoryBranchCondition bc = new SEDMemoryBranchCondition(target, parent);
      bc.setName(name);
      parent.addChild(bc);
      return bc;
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
            TestCase.assertEquals("Number of children of " + expected + " is not equal to number of children of " + current + ".", expectedChildren.length, currentChildren.length);
            for (int i = 0; i < expectedChildren.length; i++) {
               if (expectedChildren[i] instanceof ISEDBranchCondition) {
                  TestCase.assertTrue("Expected ISEDBranchCondition on " + ((ISEDBranchCondition)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDBranchCondition);
                  compareBranchCondition((ISEDBranchCondition)expectedChildren[i], (ISEDBranchCondition)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDBranchNode) {
                  TestCase.assertTrue("Expected ISEDBranchNode on " + ((ISEDBranchNode)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDBranchNode);
                  compareBranchNode((ISEDBranchNode)expectedChildren[i], (ISEDBranchNode)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDExceptionalTermination) {
                  TestCase.assertTrue("Expected ISEDExceptionalTermination on " + ((ISEDExceptionalTermination)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDExceptionalTermination);
                  compareExceptionalTermination((ISEDExceptionalTermination)expectedChildren[i], (ISEDExceptionalTermination)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDMethodCall) {
                  TestCase.assertTrue("Expected ISEDMethodCall on " + ((ISEDMethodCall)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDMethodCall);
                  compareMethodCall((ISEDMethodCall)expectedChildren[i], (ISEDMethodCall)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDMethodReturn) {
                  TestCase.assertTrue("Expected ISEDMethodReturn on " + ((ISEDMethodReturn)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDMethodReturn);
                  compareMethodReturn((ISEDMethodReturn)expectedChildren[i], (ISEDMethodReturn)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDStatement) {
                  TestCase.assertTrue("Expected ISEDStatement on " + ((ISEDStatement)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDStatement);
                  compareStatement((ISEDStatement)expectedChildren[i], (ISEDStatement)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDTermination) {
                  TestCase.assertTrue("Expected ISEDTermination on " + ((ISEDTermination)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDTermination);
                  compareTermination((ISEDTermination)expectedChildren[i], (ISEDTermination)currentChildren[i]);
               }
               else if (expectedChildren[i] instanceof ISEDThread) {
                  TestCase.assertTrue("Expected ISEDThread on " + ((ISEDThread)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDThread);
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
//System.out.println(current.getName() + " " + current.getLineNumber() + ", " + current.getCharStart() + ", " + current.getCharEnd());         
         TestCase.assertNotNull(current);
         TestCase.assertEquals(expected.getName(), current.getName());
         TestCase.assertEquals(expected.getName(), expected.getCharStart(), current.getCharStart());
         TestCase.assertEquals(expected.getName(), expected.getCharEnd(), current.getCharEnd());
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
      compareNode(expected, current, true);
   }
}
