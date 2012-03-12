package org.key_project.sed.key.core.test.util;

import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;
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
    * @throws DebugException Occurred Exception.
    */
   public static void assertInitialTarget(ISEDDebugTarget target) throws DebugException {
      TestCase.assertNotNull(target);
      TestCase.assertEquals(1, target.getSymbolicThreads().length);
      ISEDThread thread = target.getSymbolicThreads()[0];
      TestCase.assertNotNull(thread);
      TestCase.assertEquals(KeYDebugTarget.DEFAULT_THREAD_NAME, thread.getName());
      TestCase.assertEquals(0, thread.getChildren().length);
   }
   
   /**
    * Makes sure that the given {@link ISEDDebugTarget} contains the
    * symbolic execution tree of the statement example.
    * @param target The give {@link ISEDDebugTarget} to check.
    * @throws DebugException Occurred Exception.
    */
   public static void assertStatementsExample(ISEDDebugTarget target) throws DebugException {
      TestCase.assertNotNull(target);
      TestCase.assertEquals(1, target.getSymbolicThreads().length);
      ISEDThread thread = target.getSymbolicThreads()[0];
      TestCase.assertNotNull(thread);
      TestCase.assertEquals(KeYDebugTarget.DEFAULT_THREAD_NAME, thread.getName());
      TestCase.assertEquals(1, thread.getChildren().length);
      TestCase.assertTrue(thread.getChildren()[0] instanceof ISEDStatement);
      ISEDStatement s1 = (ISEDStatement)thread.getChildren()[0];
      TestCase.assertEquals("int x = 1;", s1.getName());
      TestCase.assertEquals(1, s1.getChildren().length);
      TestCase.assertTrue(s1.getChildren()[0] instanceof ISEDStatement);
      ISEDStatement s2 = (ISEDStatement)s1.getChildren()[0];
      TestCase.assertEquals("int y = 2;", s2.getName());
      TestCase.assertEquals(1, s2.getChildren().length);
      TestCase.assertTrue(s2.getChildren()[0] instanceof ISEDStatement);
      ISEDStatement s3 = (ISEDStatement)s2.getChildren()[0];
      TestCase.assertEquals("int z = 3;", s3.getName());
   }
}
