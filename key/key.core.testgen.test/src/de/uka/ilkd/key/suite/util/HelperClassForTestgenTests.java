package de.uka.ilkd.key.suite.util;

import java.io.File;

import org.key_project.util.java.IOUtil;

public class HelperClassForTestgenTests {
   public static final String TESTCASE_DIRECTORY;
   
   static {
      File projetRoot = IOUtil.getProjectRoot(HelperClassForTestgenTests.class);
      // Update path in Eclipse Plug-ins.
      if ("org.key_project.core.testgen.test".equals(projetRoot.getName())) {
         projetRoot = projetRoot.getParentFile().getParentFile().getParentFile().getParentFile();
         projetRoot = new File(projetRoot, "key" + File.separator + "key.core.testgen.test");
      }
      TESTCASE_DIRECTORY = projetRoot + File.separator + "resources"+  File.separator + "testcase";
   }
}
