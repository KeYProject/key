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
   public static final String STATEMENT_TARGET_NAME = "JML normal_behavior operation contract [id: -2147483648 / FlatSteps::doSomething]";
   
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
   public static void assertStatementsExample(ISEDDebugTarget target) throws DebugException {
      compareDebugTarget(createExpectedStatementModel(), target);
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the statement example.
    * @return The expected {@link ISEDDebugTarget}.
    */
   public static ISEDDebugTarget createExpectedStatementModel() {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(STATEMENT_TARGET_NAME);
      // Create thread
      SEDMemoryThread thread = appendThread(target);
      // Create method call
      SEDMemoryMethodCall call = appendMethodCall(target, thread, thread, "self.doSomething(_asdf,_a,_b);");
      // Create statement 1
      SEDMemoryStatement s1 = appendStatement(target, call, thread, "int x = 1;", 16);
      // Create statement 2
      SEDMemoryStatement s2 = appendStatement(target, s1, thread, "int y = 2;", 17);
      // Create statement 3
      SEDMemoryStatement s3 = appendStatement(target, s2, thread, "int z = 3;", 18);
      // Create method return
      SEDMemoryMethodReturn ret = appendMethodReturn(target, s3, thread, "self.doSomething(_asdf,_a,_b);");
      // Create termination
      appendTermination(target, ret, thread);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the else if different variables example.
    * @return The expected {@link ISEDDebugTarget}.
    */   
   public static ISEDDebugTarget createExpectedElseIfDifferentVariablesModel() {
      SEDMemoryDebugTarget target = appendDebugTarget(ELSE_IF_DIFFERENT_VARIABLES_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall call = appendMethodCall(target, thread, thread, "self.main(_a,_b);");
      
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, call, thread, "if _a true");
      SEDMemoryStatement s1 = appendStatement(target, bc1, thread, "return 1;", 5);
      SEDMemoryMethodReturn ret1 = appendMethodReturn(target, s1, thread, "self.main(_a,_b);");
      appendTermination(target, ret1, thread);

      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, call, thread, "if _a false");
      SEDMemoryBranchCondition bc2a = appendBranchCondition(target, bc2, thread, "b = TRUE TRUE");
      SEDMemoryStatement s2 = appendStatement(target, bc2a, thread, "return 2;", 8);
      SEDMemoryMethodReturn ret2 = appendMethodReturn(target, s2, thread, "self.main(_a,_b);");
      appendTermination(target, ret2, thread);

      SEDMemoryBranchCondition bc2b = appendBranchCondition(target, bc2, thread, "b = TRUE FALSE");
      SEDMemoryStatement s3 = appendStatement(target, bc2b, thread, "return 3;", 11);
      SEDMemoryMethodReturn ret3 = appendMethodReturn(target, s3, thread, "self.main(_a,_b);");
      appendTermination(target, ret3, thread);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the try catch finally example.
    * @return The expected {@link ISEDDebugTarget}.
    */
   public static ISEDDebugTarget createExpectedTryCatchFinallyModel() {
      SEDMemoryDebugTarget target = appendDebugTarget(TRY_CATCH_FINALLY_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall call = appendMethodCall(target, thread, thread, "self.tryCatchFinally(_input);");
      SEDMemoryStatement s1 = appendStatement(target, call, thread, "int result = 0;", 7);
      SEDMemoryStatement s2 = appendStatement(target, s1, thread, "result_1=1/_input;", 9);
      
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, s2, thread, "input = 0 TRUE");
      SEDMemoryBranchCondition bc1a = appendBranchCondition(target, bc1, thread, "Normal Execution (a_1 != null)");
      SEDMemoryBranchCondition bc1b = appendBranchCondition(target, bc1a, thread, "if a instanceof ArithmeticException true");
      SEDMemoryBranchCondition bc1c = appendBranchCondition(target, bc1b, thread, "Normal Execution (a instanceof ArithmeticException)");
      SEDMemoryStatement bc1S1 = appendStatement(target, bc1c, thread, "result_1=2;", 12);
      SEDMemoryStatement bc1S2 = appendStatement(target, bc1S1, thread, "result_1=result_1*2;", 15);
      SEDMemoryStatement bc1S3 = appendStatement(target, bc1S2, thread, "return result_1;", 17);
      SEDMemoryMethodReturn bc1ret = appendMethodReturn(target, bc1S3, thread, "self.tryCatchFinally(_input);");
      appendTermination(target, bc1ret, thread);
      
      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, s2, thread, "input = 0 FALSE");
      SEDMemoryStatement bc2S1 = appendStatement(target, bc2, thread, "result_1=result_1*2;", 15);
      SEDMemoryStatement bc2S2 = appendStatement(target, bc2S1, thread, "return result_1;", 17);
      SEDMemoryMethodReturn bc2ret = appendMethodReturn(target, bc2S2, thread, "self.tryCatchFinally(_input);");
      appendTermination(target, bc2ret, thread);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the static method call example.
    * @return The expected {@link ISEDDebugTarget}.
    */
   public static ISEDDebugTarget createExpectedStaticMethodCallModel() {
      SEDMemoryDebugTarget target = appendDebugTarget(STATIC_METHOD_CALL_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall mainCall = appendMethodCall(target, thread, thread, "StaticMethodCall.main();");
      SEDMemoryStatement mainS1 = appendStatement(target, mainCall, thread, "doSomething();", 30);
      SEDMemoryMethodCall doSomethingCall = appendMethodCall(target, mainS1, thread, "StaticMethodCall.doSomething();");
      SEDMemoryMethodReturn doSomethingReturn = appendMethodReturn(target, doSomethingCall, thread, "StaticMethodCall.doSomething();", 36);
      SEDMemoryStatement mainS2 = appendStatement(target, doSomethingReturn, thread, "int x = sub()+sub();", 31);
      
      SEDMemoryMethodCall subCall1 = appendMethodCall(target, mainS2, thread, "StaticMethodCall.sub();");
      SEDMemoryStatement subCall1S = appendStatement(target, subCall1, thread, "return subSub()+2;", 39);
      SEDMemoryMethodCall subSubCall1 = appendMethodCall(target, subCall1S, thread, "StaticMethodCall.subSub();");
      SEDMemoryStatement subSubCall1S = appendStatement(target, subSubCall1, thread, "return 2;", 43);
      SEDMemoryMethodReturn subSubReturn1 = appendMethodReturn(target, subSubCall1S, thread, "StaticMethodCall.subSub();");
      SEDMemoryMethodReturn subReturn1 = appendMethodReturn(target, subSubReturn1, thread, "StaticMethodCall.sub();");

      SEDMemoryMethodCall subCall2 = appendMethodCall(target, subReturn1, thread, "StaticMethodCall.sub();");
      SEDMemoryStatement subCall2S = appendStatement(target, subCall2, thread, "return subSub()+2;", 39);
      SEDMemoryMethodCall subSubCall2 = appendMethodCall(target, subCall2S, thread, "StaticMethodCall.subSub();");
      SEDMemoryStatement subSubCall2S = appendStatement(target, subSubCall2, thread, "return 2;", 43);
      SEDMemoryMethodReturn subSubReturn2 = appendMethodReturn(target, subSubCall2S, thread, "StaticMethodCall.subSub();");
      SEDMemoryMethodReturn subReturn2 = appendMethodReturn(target, subSubReturn2, thread, "StaticMethodCall.sub();");
      
      SEDMemoryStatement mainS3 = appendStatement(target, subReturn2, thread, "return x;", 32);
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, mainS3, thread, "StaticMethodCall.main();");
      appendTermination(target, mainReturn, thread);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the complex flat steps example.
    * @return The expected {@link ISEDDebugTarget}.
    */   
   public static ISEDDebugTarget createExpectedComplexFlatStepsModel() {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(COMPLEX_FLAT_STEPS_TARGET_NAME);
      // Create thread
      SEDMemoryThread thread = appendThread(target);
      // Create method call
      SEDMemoryMethodCall call = appendMethodCall(target, thread, thread, "self.doSomething();");
      // Create statement 1
      SEDMemoryStatement s1 = appendStatement(target, call, thread, "int x = 1+2;", 16);
      // Create statement 2
      SEDMemoryStatement s2 = appendStatement(target, s1, thread, "int y = 2*4*9;", 17);
      // Create statement 3
      SEDMemoryStatement s3 = appendStatement(target, s2, thread, "int z = 3*(4/(2-3));", 18);
      // Create method return
      SEDMemoryMethodReturn ret = appendMethodReturn(target, s3, thread, "self.doSomething();");
      // Create termination
      appendTermination(target, ret, thread);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the method call on object example.
    * @return The expected {@link ISEDDebugTarget}.
    */
   public static ISEDDebugTarget createExpectedMethodCallOnObjectModel() {
      SEDMemoryDebugTarget target = appendDebugTarget(METHOD_CALL_ON_OBJECT_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "MethodCallOnObject.main();");
      SEDMemoryStatement mainS1 = appendStatement(target, callMain, thread, "MethodCallOnObject x = new MethodCallOnObject ();", 4);
      SEDMemoryBranchCondition b1 = appendBranchCondition(target, mainS1, thread, "Normal Execution (m != null)");
      SEDMemoryStatement mainS2 = appendStatement(target, b1, thread, "return x.doSomething();", 5);
      SEDMemoryBranchCondition b2 = appendBranchCondition(target, mainS2, thread, "Normal Execution (x != null)");
      SEDMemoryMethodCall callDo = appendMethodCall(target, b2, thread, "x.doSomething();");
      SEDMemoryStatement doS = appendStatement(target, callDo, thread, "return 42;", 9);
      SEDMemoryMethodReturn doReturn = appendMethodReturn(target, doS, thread, "x.doSomething();");
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, doReturn, thread, "MethodCallOnObject.main();");
      appendTermination(target, mainReturn, thread);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the method call on object with exception example.
    * @return The expected {@link ISEDDebugTarget}.
    */   
   public static ISEDDebugTarget createExpectedMethodCallOnObjectWithExceptionModel() {
      SEDMemoryDebugTarget target = appendDebugTarget(METHOD_CALL_ON_OBJECT_WITH_EXCEPTION_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "MethodCallOnObjectWithException.main();");
      SEDMemoryStatement mainS1 = appendStatement(target, callMain, thread, "MethodCallOnObjectWithException x = new MethodCallOnObjectWithException ();", 5);
      SEDMemoryBranchCondition b1 = appendBranchCondition(target, mainS1, thread, "Normal Execution (m != null)");
      SEDMemoryStatement mainS2 = appendStatement(target, b1, thread, "return x.doSomething();", 6);
      SEDMemoryBranchCondition b2 = appendBranchCondition(target, mainS2, thread, "Normal Execution (x != null)");
      SEDMemoryMethodCall callDo = appendMethodCall(target, b2, thread, "x.doSomething();");
      SEDMemoryStatement doS1 = appendStatement(target, callDo, thread, "MethodCallOnObjectWithException x = null;", 15);
      SEDMemoryStatement doS2 = appendStatement(target, doS1, thread, "return x_3.return42();", 16);
      SEDMemoryBranchCondition b3 = appendBranchCondition(target, doS2, thread, "Null Reference (x_3 = null)");
      SEDMemoryBranchCondition b4 = appendBranchCondition(target, b3, thread, "Normal Execution (n_1 != null)");
//      SEDMemoryBranchCondition b5 = appendBranchCondition(target, b4, thread, "if n instanceof NullPointerException true");
      SEDMemoryBranchCondition b6 = appendBranchCondition(target, b4, thread, "Normal Execution (n instanceof NullPointerException)");
      SEDMemoryStatement mainS3 = appendStatement(target, b6, thread, "MethodCallOnObjectWithException y = new MethodCallOnObjectWithException ();", 9);
      SEDMemoryBranchCondition b7 = appendBranchCondition(target, mainS3, thread, "Normal Execution (m_3 != null)");
      SEDMemoryStatement mainS4 = appendStatement(target, b7, thread, "return y.return42();", 10);
      SEDMemoryBranchCondition b8 = appendBranchCondition(target, mainS4, thread, "Normal Execution (y != null)");
      SEDMemoryMethodCall call42 = appendMethodCall(target, b8, thread, "y.return42();");
      SEDMemoryStatement return42S = appendStatement(target, call42, thread, "return 42;", 20);
      SEDMemoryMethodReturn call42Return = appendMethodReturn(target, return42S, thread, "y.return42();");
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, call42Return, thread, "MethodCallOnObjectWithException.main();");
      appendTermination(target, mainReturn, thread);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the method call parallel example.
    * @return The expected {@link ISEDDebugTarget}.
    */
   public static ISEDDebugTarget createExpectedMethodCallParallelModel() {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(METHOD_CALL_PARALLEL_TARGET_NAME);
      // Create thread
      SEDMemoryThread thread = appendThread(target);
      // Create method call main
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "self.main();");
      // Create statement a()
      SEDMemoryStatement mainStatement1 = appendStatement(target, callMain, thread, "int a = a();", 4); 
      // Create method call a
      SEDMemoryMethodCall callA = appendMethodCall(target, mainStatement1, thread, "self.a();");
      // Create statement b()
      SEDMemoryStatement aStatement1 = appendStatement(target, callA, thread, "int b1 = b();", 10); 
      // Create method call b
      SEDMemoryMethodCall callB = appendMethodCall(target, aStatement1, thread, "self.b();");
      // Create statement c()
      SEDMemoryStatement bStatement = appendStatement(target, callB, thread, "return c();", 17); 
      // Create method call c
      SEDMemoryMethodCall callC = appendMethodCall(target, bStatement, thread, "self.c();");
      // Create statement 42
      SEDMemoryStatement fourtyTwoStatement = appendStatement(target, callC, thread, "return 42;", 21); 
      // Create method return of c
      SEDMemoryMethodReturn cReturn = appendMethodReturn(target, fourtyTwoStatement, thread, "self.c();");
      // Create method return of b
      SEDMemoryMethodReturn bReturn = appendMethodReturn(target, cReturn, thread, "self.b();"); 
      // Create statement b()
      SEDMemoryStatement aStatement2 = appendStatement(target, bReturn, thread, "int b2 = b();", 11); 
      // Create method call b
      SEDMemoryMethodCall callB2 = appendMethodCall(target, aStatement2, thread, "self.b();"); ;
      // Create statement c()
      SEDMemoryStatement bStatement2 = appendStatement(target, callB2, thread, "return c();", 17);
      // Create method call c
      SEDMemoryMethodCall callC2 = appendMethodCall(target, bStatement2, thread, "self.c();"); 
      // Create statement 42
      SEDMemoryStatement fourtyTwoStatement2 = appendStatement(target, callC2, thread, "return 42;", 21); 
      // Create method return of c
      SEDMemoryMethodReturn cReturn2 = appendMethodReturn(target, fourtyTwoStatement2, thread, "self.c();"); 
      // Create method return of b
      SEDMemoryMethodReturn bReturn2 = appendMethodReturn(target, cReturn2, thread, "self.b();"); 
      // Create statement c()
      SEDMemoryStatement aStatement3 = appendStatement(target, bReturn2, thread, "int c = c();", 12); 
      // Create method call c
      SEDMemoryMethodCall callC3 = appendMethodCall(target, aStatement3, thread, "self.c();"); ;
      // Create statement 42
      SEDMemoryStatement fourtyTwoStatement3 = appendStatement(target, callC3, thread, "return 42;", 21); 
      // Create method return of c
      SEDMemoryMethodReturn cReturn3 = appendMethodReturn(target, fourtyTwoStatement3, thread, "self.c();"); 
      // Create statement return
      SEDMemoryStatement aStatement4 = appendStatement(target, cReturn3, thread, "return b1+b2+c;", 13); 
      // Create method return of a
      SEDMemoryMethodReturn aReturn = appendMethodReturn(target, aStatement4, thread, "self.a();"); 
      // Create statement x()
      SEDMemoryStatement mainStatement2 = appendStatement(target, aReturn, thread, "int x = x();", 5); 
      // Create method call x
      SEDMemoryMethodCall callX = appendMethodCall(target, mainStatement2, thread, "self.x();");
      // Create statement 42
      SEDMemoryStatement twoStatement = appendStatement(target, callX, thread, "return 2;", 25);
      // Create method return of c
      SEDMemoryMethodReturn xReturn = appendMethodReturn(target, twoStatement, thread, "self.x();"); 
      // Create statement return
      SEDMemoryStatement mainStatement3 = appendStatement(target, xReturn, thread, "return a*x;", 6);
      // Create method return
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, mainStatement3, thread, "self.main();");
      // Create termination
      appendTermination(target, mainReturn, thread);
      return target;
   }
   
   /**
    * Creates the expected {@link ISEDDebugTarget} for the simple if example.
    * @return The expected {@link ISEDDebugTarget}.
    */
   public static ISEDDebugTarget createExpectedSimpleIfModel() {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(SIMPLE_IF_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall callMin = appendMethodCall(target, thread, thread, "self.min(_i,_j);");
      SEDMemoryStatement s1 = appendStatement(target, callMin, thread, "int result;", 23);
      SEDMemoryBranchNode branchNode = appendBranchNode(target, s1, thread, "if (_i<_j) {   result_1=_i; }else  {   result_1=_j; }", 29);
      // Branch 1
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, branchNode, thread, "j >= 1 + i TRUE");
      SEDMemoryStatement s2 = appendStatement(target, bc1, thread, "result_1=_i;", 25);
      SEDMemoryStatement s3 = appendStatement(target, s2, thread, "return result_1;", 30);
      SEDMemoryMethodReturn minReturn1 = appendMethodReturn(target, s3, thread, "self.min(_i,_j);");
      appendTermination(target, minReturn1, thread);
      // Branch 2
      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, branchNode, thread, "j >= 1 + i FALSE");
      SEDMemoryStatement s4 = appendStatement(target, bc2, thread, "result_1=_j;", 28);
      SEDMemoryStatement s5 = appendStatement(target, s4, thread, "return result_1;", 30);
      SEDMemoryMethodReturn minReturn2 = appendMethodReturn(target, s5, thread, "self.min(_i,_j);");
      appendTermination(target, minReturn2, thread);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the functional if example.
    * @return The expected {@link ISEDDebugTarget}.
    */
   public static ISEDDebugTarget createExpectedFunctionalIfModel() {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(FUNCTIONAL_IF_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall callMin = appendMethodCall(target, thread, thread, "self.min(_i,_j);");
      SEDMemoryStatement s1 = appendStatement(target, callMin, thread, "int result;", 29);
      SEDMemoryBranchNode branchNode = appendBranchNode(target, s1, thread, "if (invert(_i)<invert(_j)) {   result_1=_i; }else  {   result_1=_j; }", 35);
      SEDMemoryMethodCall callInvert1 = appendMethodCall(target, branchNode, thread, "self.invert(a);");
      SEDMemoryStatement callS1 = appendStatement(target, callInvert1, thread, "return a*-1;", 40);
      SEDMemoryMethodReturn returnInvert1 = appendMethodReturn(target, callS1, thread, "self.invert(a);");
      SEDMemoryMethodCall callInvert2 = appendMethodCall(target, returnInvert1, thread, "self.invert(a_1);");
      SEDMemoryStatement callS2 = appendStatement(target, callInvert2, thread, "return a_1*-1;", 40);
      SEDMemoryMethodReturn returnInvert2 = appendMethodReturn(target, callS2, thread, "self.invert(a_1);");
      // Branch 1
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, returnInvert2, thread, "j <= -1 + i TRUE");
      SEDMemoryStatement s2 = appendStatement(target, bc1, thread, "result_1=_i;", 31);
      SEDMemoryStatement s3 = appendStatement(target, s2, thread, "return result_1;", 36);
      SEDMemoryMethodReturn minReturn1 = appendMethodReturn(target, s3, thread, "self.min(_i,_j);");
      appendTermination(target, minReturn1, thread);
      // Branch 2
      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, returnInvert2, thread, "j <= -1 + i FALSE");
      SEDMemoryStatement s4 = appendStatement(target, bc2, thread, "result_1=_j;", 34);
      SEDMemoryStatement s5 = appendStatement(target, s4, thread, "return result_1;", 36);
      SEDMemoryMethodReturn minReturn2 = appendMethodReturn(target, s5, thread, "self.min(_i,_j);");
      appendTermination(target, minReturn2, thread);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the complex if example.
    * @return The expected {@link ISEDDebugTarget}.
    */   
   public static ISEDDebugTarget createExpectedComplexIfModel() {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(COMPLEX_IF_TARGET_NAME);
      SEDMemoryThread thread = appendThread(target);
      SEDMemoryMethodCall callMin = appendMethodCall(target, thread, thread, "self.min(_i,_j);");
      SEDMemoryStatement s1 = appendStatement(target, callMin, thread, "int result;", 23);
      SEDMemoryBranchNode branchNode = appendBranchNode(target, s1, thread, "if (_i<_j&&_i!=_j) {   result_1=_i; }else  {   result_1=_j; }", 29);
      // Branch 1
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, branchNode, thread, "j >= 1 + i TRUE");
      SEDMemoryBranchCondition bc1a = appendBranchCondition(target, bc1, thread, "if x_2 true");
      SEDMemoryStatement s2 = appendStatement(target, bc1a, thread, "result_1=_i;", 25);
      SEDMemoryStatement s3 = appendStatement(target, s2, thread, "return result_1;", 30);
      SEDMemoryMethodReturn minReturn1 = appendMethodReturn(target, s3, thread, "self.min(_i,_j);");
      appendTermination(target, minReturn1, thread);
      // Branch 2
      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, branchNode, thread, "j >= 1 + i FALSE");
      SEDMemoryStatement s4 = appendStatement(target, bc2, thread, "result_1=_j;", 28);
      SEDMemoryStatement s5 = appendStatement(target, s4, thread, "return result_1;", 30);
      SEDMemoryMethodReturn minReturn2 = appendMethodReturn(target, s5, thread, "self.min(_i,_j);");
      appendTermination(target, minReturn2, thread);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the method call hierarchy example.
    * @return The expected {@link ISEDDebugTarget}.
    */
   public static ISEDDebugTarget createExpectedMethodCallHierarchyModel() {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(METHOD_CALL_HIERARCHY_TARGET_NAME);
      // Create thread
      SEDMemoryThread thread = appendThread(target);
      // Create method call main
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "self.main();");
      // Create statement a()
      SEDMemoryStatement mainStatement = appendStatement(target, callMain, thread, "return a();", 4);
      // Create method call a
      SEDMemoryMethodCall callA = appendMethodCall(target, mainStatement, thread, "self.a();");
      // Create statement b()
      SEDMemoryStatement aStatement = appendStatement(target, callA, thread, "return b();", 8);
      // Create method call b
      SEDMemoryMethodCall callB = appendMethodCall(target, aStatement, thread, "self.b();");
      // Create statement c()
      SEDMemoryStatement bStatement = appendStatement(target, callB, thread, "return c();", 12);
      // Create method call c
      SEDMemoryMethodCall callC = appendMethodCall(target, bStatement, thread, "self.c();");
      // Create statement 42
      SEDMemoryStatement fourtyTwoStatement = appendStatement(target, callC, thread, "return 42;", 16);
      // Create method return of c
      SEDMemoryMethodReturn cReturn = appendMethodReturn(target, fourtyTwoStatement, thread, "self.c();");
      // Create method return of b
      SEDMemoryMethodReturn bReturn = appendMethodReturn(target, cReturn, thread, "self.b();");
      // Create method return of a
      SEDMemoryMethodReturn aReturn = appendMethodReturn(target, bReturn, thread, "self.a();");
      // Create method return
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, aReturn, thread, "self.main();");
      // Create termination
      appendTermination(target, mainReturn, thread);
      return target;
   }

   /**
    * Creates the expected {@link ISEDDebugTarget} for the method call hierarchy with exception example.
    * @return The expected {@link ISEDDebugTarget}.
    */   
   public static ISEDDebugTarget createExpectedMethodCallHierarchyWithExceptionModel() {
      // Create target
      SEDMemoryDebugTarget target = appendDebugTarget(METHOD_CALL_HIERARCHY_WITH_EXCEPTION_TARGET_NAME);
      // Create thread
      SEDMemoryThread thread = appendThread(target);
      // Create method call main
      SEDMemoryMethodCall callMain = appendMethodCall(target, thread, thread, "self.main();");
      // Create statement a()
      SEDMemoryStatement mainStatement = appendStatement(target, callMain, thread, "a();", 7);
      // Create method call a
      SEDMemoryMethodCall callA = appendMethodCall(target, mainStatement, thread, "self.a();");
      // Create statement b()
      SEDMemoryStatement aStatement = appendStatement(target, callA, thread, "b();", 12);
      // Create method call b
      SEDMemoryMethodCall callB = appendMethodCall(target, aStatement, thread, "self.b();");
      // Create statement c()
      SEDMemoryStatement bStatement = appendStatement(target, callB, thread, "c();", 21);
      // Create method call c
      SEDMemoryMethodCall callC = appendMethodCall(target, bStatement, thread, "self.c();");
      // Create statement 42
      SEDMemoryStatement throwStatement = appendStatement(target, callC, thread, "throw new RuntimeException ();", 25);
      // Create branch condition 1
      SEDMemoryBranchCondition bc1 = appendBranchCondition(target, throwStatement, thread, "Normal Execution (r_1 != null)");
      // Create branch condition 2
      SEDMemoryBranchCondition bc2 = appendBranchCondition(target, bc1, thread, "Normal Execution (r instanceof RuntimeException)");
      // Create statement ae assignment
      SEDMemoryStatement aeAssignmentStatement = appendStatement(target, bc2, thread, "int ae = -1;", 15);
      // Create statement a assignment
      SEDMemoryStatement aAssignmentStatement = appendStatement(target, aeAssignmentStatement, thread, "int a1 = 1;", 17);
      // Create method return of a
      SEDMemoryMethodReturn aReturn = appendMethodReturn(target, aAssignmentStatement, thread, "self.a();");
      // Create method return
      SEDMemoryMethodReturn mainReturn = appendMethodReturn(target, aReturn, thread, "self.main();");
      // Create termination
      appendTermination(target, mainReturn, thread);
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
    * @return The created {@link SEDMemoryMethodCall}.
    */
   public static SEDMemoryMethodCall appendMethodCall(ISEDDebugTarget target, 
                                                      ISEDMemoryDebugNode parent, 
                                                      ISEDThread thread,
                                                      String name) {
      SEDMemoryMethodCall methodCall = new SEDMemoryMethodCall(target, parent, thread);
      methodCall.setName(name);
      parent.addChild(methodCall);
      return methodCall;
   }
   
   /**
    * Appends a new statement to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @param thread The {@link ISEDThread} to use.
    * @param name The name to set on the created {@link SEDMemoryStatement}.
    * @param lineNumber The line number to set on the created {@link SEDMemoryStatement}
    * @return The created {@link SEDMemoryStatement}.
    */
   public static SEDMemoryStatement appendStatement(ISEDDebugTarget target, 
                                                    ISEDMemoryDebugNode parent, 
                                                    ISEDThread thread,
                                                    String name,
                                                    int lineNumber) {
      SEDMemoryStatement statement = new SEDMemoryStatement(target, parent, thread);
      statement.setName(name);
      statement.setLineNumber(lineNumber);
      parent.addChild(statement);
      return statement;
   }
   
   /**
    * Appends a new method return to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @param thread The {@link ISEDThread} to use.
    * @param name The name to set on the created {@link SEDMemoryMethodReturn}.
    * @return The created {@link SEDMemoryMethodReturn}.
    */
   public static SEDMemoryMethodReturn appendMethodReturn(ISEDDebugTarget target, 
                                                          ISEDMemoryDebugNode parent, 
                                                          ISEDThread thread,
                                                          String name) {
      return appendMethodReturn(target, parent, thread, name, -1);
   }
   
   /**
    * Appends a new method return to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @param thread The {@link ISEDThread} to use.
    * @param name The name to set on the created {@link SEDMemoryMethodReturn}.
    * @param lineNumber The line number to set on the created {@link SEDMemoryMethodReturn}.
    * @return The created {@link SEDMemoryMethodReturn}.
    */
   public static SEDMemoryMethodReturn appendMethodReturn(ISEDDebugTarget target, 
                                                          ISEDMemoryDebugNode parent, 
                                                          ISEDThread thread,
                                                          String name,
                                                          int lineNumber) {
      SEDMemoryMethodReturn methodReturn = new SEDMemoryMethodReturn(target, parent, thread);
      methodReturn.setName(KeYDebugTarget.createMethodReturnName(null, name));
      methodReturn.setLineNumber(lineNumber);
      parent.addChild(methodReturn);
      return methodReturn;
   }
   
   /**
    * Appends a new termination to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @param thread The {@link ISEDThread} to use.
    * @return The created {@link SEDMemoryTermination}.
    */
   public static SEDMemoryTermination appendTermination(ISEDDebugTarget target, 
                                                        ISEDMemoryDebugNode parent, 
                                                        ISEDThread thread) {
      SEDMemoryTermination termination = new SEDMemoryTermination(target, parent, thread);
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
    * @return The created {@link SEDMemoryBranchNode}.
    */
   public static SEDMemoryBranchNode appendBranchNode(ISEDDebugTarget target, 
                                                      ISEDMemoryDebugNode parent, 
                                                      ISEDThread thread,
                                                      String name) {
      return appendBranchNode(target, parent, thread, name, -1);
   }
   
   /**
    * Appends a new branch node to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @param thread The {@link ISEDThread} to use.
    * @param name The name to set on the created {@link SEDMemoryBranchNode}.
    * @param lineNumber The line number to set on the created {@link SEDMemoryBranchNode}.
    * @return The created {@link SEDMemoryBranchNode}.
    */
   public static SEDMemoryBranchNode appendBranchNode(ISEDDebugTarget target, 
                                                      ISEDMemoryDebugNode parent, 
                                                      ISEDThread thread,
                                                      String name,
                                                      int lineNumber) {
      SEDMemoryBranchNode bn = new SEDMemoryBranchNode(target, parent, thread);
      bn.setName(name);
      bn.setLineNumber(lineNumber);
      parent.addChild(bn);
      return bn;
   }
   
   /**
    * Appends a new branch condition to the given parent {@link ISEDMemoryDebugNode}.
    * @param target The {@link ISEDDebugTarget} to use.
    * @param parent The parent {@link ISEDMemoryDebugNode} to append to.
    * @param thread The {@link ISEDThread} to use.
    * @param name The name to set on the created {@link SEDMemoryBranchCondition}.
    * @return The created {@link SEDMemoryBranchCondition}.
    */
   public static SEDMemoryBranchCondition appendBranchCondition(ISEDDebugTarget target, 
                                                                ISEDMemoryDebugNode parent, 
                                                                ISEDThread thread,
                                                                String name) {
      SEDMemoryBranchCondition bc = new SEDMemoryBranchCondition(target, parent, thread);
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
