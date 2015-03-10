package de.uka.ilkd.key.suite.util;

import java.io.File;

import org.key_project.util.java.IOUtil;

public class HelperClassForTestgenTests {
   public static final String TESTCASE_DIRECTORY;
   
   static {
      File projectRoot = IOUtil.getProjectRoot(HelperClassForTestgenTests.class);
      // Update path in Eclipse Plug-ins executed as JUnit Test.
      if ("org.key_project.core.testgen.test".equals(projectRoot.getName())) {
         projectRoot = projectRoot.getParentFile().getParentFile().getParentFile().getParentFile();
         projectRoot = new File(projectRoot, "key" + File.separator + "key.core.testgen.test");
      }
      // Update path in Eclipse Plug-ins executed as JUnit Plug-in Test.
      else if ("tests".equals(projectRoot.getName())) {
         projectRoot = projectRoot.getParentFile().getParentFile().getParentFile();
         projectRoot = new File(projectRoot, "key" + File.separator + "key.core.testgen.test");
      }
      TESTCASE_DIRECTORY = projectRoot + File.separator + "resources"+  File.separator + "testcase";
   }
}
