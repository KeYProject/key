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

package org.key_project.sed.ui.visualization.test.testcase;

import java.io.File;

import junit.framework.TestCase;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.sourcelookup.containers.LocalFileStorage;
import org.junit.Test;
import org.key_project.sed.ui.visualization.launch.AbsoluteFileSystemPathSourceContainer;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * Tests for {@link AbsoluteFileSystemPathSourceContainer}.
 * @author Martin Hentschel
 */
public class AbsoluteFileSystemPathSourceContainerTest extends TestCase {
   /**
    * Tests {@link AbsoluteFileSystemPathSourceContainer#findSourceElements(String)} 
    * with existing and not existing files and folders.
    */
   @Test
   public void testFindSourceElements() throws Exception {
      File tmpFile = null;
      File tmpDir = null;
      try {
         tmpFile = File.createTempFile("AbsoluteFileSystemPathSourceContainerTest", ".txt");
         tmpDir = IOUtil.createTempDirectory("AbsoluteFileSystemPathSourceContainerTest", "directory");
         // Test existing stuff
         doFileTest(tmpFile);
         doFileTest(tmpDir);
         // Test not existing stuff
         doFileTest(new File(tmpDir, "NotExistingFolder"));
         // Test null
         doFileTest(null);         
      }
      finally {
         IOUtil.delete(tmpFile);
         IOUtil.delete(tmpDir);
      }
   }
   
   /**
    * Executes test steps used by {@link #testFindSourceElements()}.
    * @param file The {@link File} to test.
    * @throws CoreException Occurred Exception.
    */
   protected void doFileTest(File file) throws CoreException {
      Object[] result = AbsoluteFileSystemPathSourceContainer.INSTANCE.findSourceElements(ObjectUtil.toString(file));
      if (file != null && file.exists()) {
         assertNotNull(result);
         assertEquals(1, result.length);
         assertTrue(result[0] instanceof LocalFileStorage);
         assertEquals(file, ((LocalFileStorage)result[0]).getFile());
      }
      else {
         assertSame(AbsoluteFileSystemPathSourceContainer.EMPTY, result);
      }
   }
}