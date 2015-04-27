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

package org.key_project.ui.test.testcase;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.Properties;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.ui.test.Activator;
import org.key_project.ui.util.KeYExampleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.KeYEnvironment;

/**
 * Contains tests for {@link KeYExampleUtil}.
 * @author Martin Hentschel
 */
public class KeYExampleUtilTest extends AbstractSetupTestCase {
    /**
     * Tests {@link KeYExampleUtil#getExampleProof()}.
     */
    @Test
    public void testGetExampleProof() throws Exception {
       // Get value
       File file = KeYExampleUtil.getExampleProof();
       // Test file
       assertNotNull(file);
       assertTrue(file.exists());
       assertTrue(file.isFile());
       // Load file
       KeYEnvironment<?> env = KeYEnvironment.load(file, null, null, null);
       env.dispose();
    }

    /**
     * Tests {@link KeYExampleUtil#getLocalExampleDirectory()}.
     */
    @Test
    public void testGetLocalExampleDirectory() throws IOException {
        // Get value
        String localExampleDir = KeYExampleUtil.getLocalExampleDirectory();
        // Compare value
        assertNotNull(localExampleDir);
        File file = new File(localExampleDir);
        assertTrue(file.exists());
        assertTrue(file.isDirectory());
        File firstTouch = new File(file, "firstTouch"); // Ensure that it is the right folder
        assertTrue(firstTouch.exists());
        assertTrue(firstTouch.isDirectory());
    }
    
    /**
     * Tests {@link KeYExampleUtil#updateExampleDirectory(String, String, String, String, String)}.
     */
    @Test
    public void testUpdateExampleDirectory() throws CoreException, IOException {
        // Create target to use as example.
        IProject project = TestUtilsUtil.createProject("KeYExampleUtilTest_testUpdateExampleDirectory");
        File projectLocation = ResourceUtil.getLocation(project);
        File exampleDir = new File(projectLocation, "example");
        File exampleFile = new File(projectLocation, "example.properties");
        assertFalse(exampleDir.exists());
        assertFalse(exampleFile.exists());
        // Test initial creation
        KeYExampleUtil.updateExampleDirectory("1", Activator.PLUGIN_ID, "data/ExampleContent1", exampleFile.getAbsolutePath(), exampleDir.getAbsolutePath());
        assertExampleDirectory(exampleDir, exampleFile, "1", "ExampleFile1.txt");
        // Test same version again
        KeYExampleUtil.updateExampleDirectory("1", Activator.PLUGIN_ID, "data/ExampleContent1", exampleFile.getAbsolutePath(), exampleDir.getAbsolutePath());
        assertExampleDirectory(exampleDir, exampleFile, "1", "ExampleFile1.txt");
        // Test different version
        KeYExampleUtil.updateExampleDirectory("2", Activator.PLUGIN_ID, "data/ExampleContent2", exampleFile.getAbsolutePath(), exampleDir.getAbsolutePath());
        assertExampleDirectory(exampleDir, exampleFile, "2", "ExampleFile2.txt", "ExampleFile3.txt");
        // Test different version again
        KeYExampleUtil.updateExampleDirectory("2", Activator.PLUGIN_ID, "data/ExampleContent2", exampleFile.getAbsolutePath(), exampleDir.getAbsolutePath());
        assertExampleDirectory(exampleDir, exampleFile, "2", "ExampleFile2.txt", "ExampleFile3.txt");
        // Test initial version again
        KeYExampleUtil.updateExampleDirectory("1", Activator.PLUGIN_ID, "data/ExampleContent1", exampleFile.getAbsolutePath(), exampleDir.getAbsolutePath());
        assertExampleDirectory(exampleDir, exampleFile, "1", "ExampleFile1.txt");
    }
    
    /**
     * Makes sure that the correct example content exists.
     * @param exampleDir The example directory to check.
     * @param exampleFile The example file to check.
     * @param expectedVersion The expected version.
     * @param expectedFiles The expected files in the example directory.
     * @throws IOException Occurred Exception.
     */
    protected void assertExampleDirectory(File exampleDir, 
                                          File exampleFile, 
                                          String expectedVersion, 
                                          String... expectedFiles) throws IOException {
        // Test example directory
        assertTrue(exampleDir.exists());
        File[] files = exampleDir.listFiles();
        assertNotNull(files);
        Arrays.sort(files);
        assertEquals(expectedFiles.length, files.length);
        for (int i = 0; i < files.length; i++) {
            assertEquals(files[i].getName(), expectedFiles[i]);
            assertEquals(expectedFiles[i], IOUtil.readFrom(new FileInputStream(files[i])));
        }
        // Test example file
        assertTrue(exampleFile.exists());
        Properties properties = new Properties();
        properties.load(new FileInputStream(exampleFile));
        assertEquals(expectedVersion, properties.get(KeYExampleUtil.VERSION_KEY));
    }

    /**
     * Executes assertions to make sure that the correct files are extracted
     * for {@link #testExtractFromBundleToFilesystem()}. 
     * @param folder The target folder.
     * @throws IOException Occurred Exception
     */
    protected static void doTestExtractFromBundleToFilesystem(File folder) throws IOException {
       // Test container
       assertNotNull(folder);
       assertTrue(folder.exists());
       assertTrue(folder.isDirectory());
       // Test container/File.txt
       File file = new File(folder, "File.txt");
       assertTrue(file.exists());
       assertTrue(file.isFile());
       assertEquals("File", IOUtil.readFrom(new FileInputStream(file)));
       // Test container/EmptyFolder
       // Test container/SubFolder
       File subFolder = new File(folder, "SubFolder");
       assertTrue(subFolder.exists());
       assertTrue(subFolder.isDirectory());
       // Test container/SubFolder/EmptySubFolder
       // Test container/SubFolder/SubSubFolder
       File subSubFolder = new File(subFolder, "SubSubFolder");
       assertTrue(subSubFolder.exists());
       assertTrue(subSubFolder.isDirectory());
       // Test container/SubFolder/SubSubFolder/EmptySubSubFolder
       // Test container/SubFolder/SubSubFolder/SubSubFile.txt
       File subSubFile = new File(subSubFolder, "SubSubFile.txt");
       assertTrue(subSubFile.exists());
       assertTrue(subSubFile.isFile());
       assertEquals("SubSubFile", IOUtil.readFrom(new FileInputStream(subSubFile)));
       // Test container/SubFolder/SubFile.txt
       File subFile = new File(subFolder, "SubFile.txt");
       assertTrue(subFile.exists());
       assertTrue(subFile.isFile());
       assertEquals("SubFile", IOUtil.readFrom(new FileInputStream(subFile)));
    }
}