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

package org.key_project.key4eclipse.test.testcase;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.key_project.key4eclipse.test.suite.CustomParameterized;
import org.key_project.key4eclipse.test.suite.CustomParameterized.CustomParameters;
import org.key_project.key4eclipse.util.KeYExampleUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.core.Main;

/**
 * <p>
 * This class uses the provided example files from KeY for test purpose
 * on the same way as the bin/runAllProofs.pl does it.
 * </p>
 * <p>
 * The files to test are listed in files:
 * <ul>
 *    <li>examples/index/automaticJAVADL.txt (Proof should pass)</li>
 *    <li>examples/index/notProvableJavaDL.txt (Proof should fail)</li>
 * </ul>
 * </p>
 * <p>
 * The test steps for each defined test file are:
 * <ol>
 *    <li>Create a copy with extension ".auto.key". The file contains the default settings from examples/index/headerJavaDL.txt if required.</li>
 *    <li>A new Java process is started for each test file. It executes {@link Main#main(String[])} with the file as parameter and additional parameter {@code auto}.</li>
 *    <li>The process termination result must be {@code 0} if the proof is closed and something different otherwise. This value is used to determine the test result.</li>
 * </ol> 
 * </p>
 * <p>
 * This class can be executed as "JUnit plug-in test" without extra configurations.
 * For execution as normal "Junit test" it is required to define the system
 * properties "key.home" and "key.lib" like:
 * {@code "-Dkey.home=D:/Forschung/GIT/KeY" "-Dkey.lib=D:/Forschung/Tools/KeY-External Libs"}.
 * </p>
 * @author Martin Hentschel
 */
@RunWith(CustomParameterized.class)
public class RunAllProofsTest extends TestCase {
    /**
     * The path to the KeY repository. 
     * Configurable via system property {@code key.home}.
     */
    private static final String KEY_HOME;
    
    /**
     * The path to the KeY external libraries. 
     * Configurable via system property {@code key.lib}.
     */
    private static final String KEY_LIB_DIR;
    
    /**
     * Computes the constant values.
     */
    static {
        // Compute path to the KeY repository.
        String keyHome = System.getProperty("key.home");
        if (StringUtil.isEmpty(keyHome)) {
            keyHome = KeYExampleUtil.getLocalKeYHomeDirectory();
        }
        KEY_HOME = keyHome;
        // Compute path to the KeY external libraries.
        String libDir = System.getProperty("key.lib");
        if (StringUtil.isEmpty(libDir)) {
            libDir = KeYExampleUtil.getLocalKeYExtraLibsDirectory();
        }
        KEY_LIB_DIR = libDir;
    }
    
    /**
     * The current file to test.
     */
    private File testFile;

    /**
     * The default header to use.
     */
    private String defaultHeader;
    
    /**
     * The expected result.
     */
    private boolean successExpected;

    /**
     * Constructor.
     * @param testFile The current file to test.
     * @param defaultHeader The default header to use.
     * @param successExpected The expected result.
     */
    public RunAllProofsTest(File testFile, String defaultHeader, boolean successExpected) {
        this.testFile = testFile;
        this.defaultHeader = defaultHeader;
        this.successExpected = successExpected;
    }

    /**
     * Tests each file defined by the instance variables. The tests steps
     * are described in the constructor of this class.
     * @throws Exception
     */
    @Test
    public void testWithKeYAutoMode() throws Exception {
        // Print information for user
        System.out.println();
        System.out.println();
        System.out.println("Testing: " + testFile.getAbsolutePath());
        // Make sure that valid file is defined
        assertNotNull(testFile);
        assertTrue(testFile.exists());
        assertFalse("KEY_HOME is not defined.", StringUtil.isTrimmedEmpty(KEY_HOME));
        assertFalse("KEY_LIB_DIR is not defined.", StringUtil.isTrimmedEmpty(KEY_LIB_DIR));
        assertTrue("KEY_HOME directory \"" + KEY_HOME + "\" does not exist.", new File(KEY_HOME).isDirectory());
        assertTrue("KEY_LIB_DIR directory \"" + KEY_LIB_DIR + "\" does not exist.", new File(KEY_LIB_DIR).isDirectory());
        // Prepare file for testing
        File fileToTest = prepareFile(testFile);
        // Compute directory that contains the compiled KeY classes
        String keyBinaries = KEY_HOME + File.separator + "system" + File.separator + "binary";
        // Start process
        ProcessBuilder sb = new ProcessBuilder("java", 
                                               "-cp", "\"" + keyBinaries + "\";\"" + KEY_LIB_DIR + File.separator + "antlr.jar\";\"" + KEY_LIB_DIR + File.separator + "javacc.jar\";\"" + KEY_LIB_DIR + File.separator + "junit.jar\";\"" + KEY_LIB_DIR + File.separator + "objenesis.jar\";\"" + KEY_LIB_DIR + File.separator + "recoderKey.jar\"", 
                                               "de.uka.ilkd.key.gui.Main",
                                               fileToTest.getAbsolutePath(), 
                                               "auto");
        System.out.println("Starting process: " + sb.command());
        Process process = sb.start();
        InputStream in = process.getInputStream();
        InputStream err = process.getErrorStream();
        while (isAlive(process)) {
            copyStream(in, System.out);
            copyStream(err, System.err);
            Thread.sleep(100);
        }
        if (successExpected) {
            assertSame(0, process.exitValue());
        }
        else {
            assertNotSame(0, process.exitValue());
        }
    }
    
    /**
     * Utility method to create a copy of the given file with file extension
     * {@code .auto.key}. The file contains the same content as the given one
     * but is may enriched with the default settings defined via
     * {@code examples/index/headerJavaDL.txt}.
     * @param toPrepare The {@link File} to prepare.
     * @return The prepared {@link File}.
     * @throws IOException Occurred Exception.
     */
    protected File prepareFile(File toPrepare) throws IOException {
        String originalContent = IOUtil.readFrom(new FileInputStream(toPrepare));
        if (!originalContent.contains("\\settings")) {
            originalContent = defaultHeader + originalContent;
        }
        File preparedFile = new File(toPrepare.toString() + ".auto.key");
        if (preparedFile.exists()) {
            IOUtil.delete(preparedFile);
        }
        IOUtil.writeTo(new FileOutputStream(preparedFile, false), originalContent);
        return preparedFile;
    }

    /**
     * Checks if the given {@link Process} is still alive.
     * @param process The {@link Process} to check.
     * @return {@code true} alive, {@code false} finished.
     */
    protected boolean isAlive(Process process) {
        try {
            process.exitValue();
            return false;
        }
        catch (Exception e) {
            return true;
        }
    }

    /**
     * Copies the content from the given {@link InputStream} to
     * the {@link OutputStream}.
     * @param in The {@link InputStream} to read from.
     * @param out The {@link OutputStream} to copy to.
     * @throws IOException Occurred Exception.
     */
    protected void copyStream(InputStream in, OutputStream out) throws IOException {
        while (in.available() >= 1) {
            byte[] buffer = new byte[1024];
            int read = 0;
            while ((read = in.read(buffer)) > 0) {
                out.write(buffer, 0, read);
            }
        }
    }
    
    /**
     * Collects all test files. Instances of this class are automatically
     * created with the returned parameters by the JUnit test suite
     * {@link CustomParameters}.
     * @return The parameters. Each row will be one test case.
     * @throws IOException Occurred Exception.
     */
    @CustomParameters
    public static Collection<Object[]> data() throws IOException {
        // Make sure that required parameters are defined
        assertFalse("KEY_HOME is not defined.", StringUtil.isTrimmedEmpty(KEY_HOME));
        assertTrue("KEY_HOME directory \"" + KEY_HOME + "\" does not exist.", new File(KEY_HOME).isDirectory());
        // Get example directory
        File exampleDir = new File(KEY_HOME, "examples");
        assertTrue("Directory \"" + exampleDir + "\" does not exist.", exampleDir.isDirectory());
        // Read default header
        String defaultHeader = IOUtil.readFrom(new FileInputStream(new File(exampleDir, "index/headerJavaDL.txt")));
        // Collect test files
        Collection<Object[]> data = new LinkedList<Object[]>();
        data.addAll(dataFromFile(defaultHeader, exampleDir, new File(exampleDir, "index/automaticJAVADL.txt")));
        return data;
    }
    
    /**
     * Lists the contained test files.
     * @param defaultHeader The default header to use.
     * @param exampleDir The example directory to use.
     * @param indexFile The index file to read test files from.
     * @param successExpected Expected system exit value in a test.
     * @return The created parameters.
     * @throws IOException Occurred Exception.
     */
    protected static List<Object[]> dataFromFile(String defaultHeader, File exampleDir, File indexFile) throws IOException {
        List<Object[]> result = new LinkedList<Object[]>();
        if (indexFile.isFile()) {
           BufferedReader reader = new BufferedReader(new FileReader(indexFile));
           try {
               String line = null;
               while ((line = reader.readLine()) != null) {
                   if (line.startsWith("./")) {
                       line = line.substring("./".length());
                   }
                   int indexSeparator = line.indexOf(":");
                   if (indexSeparator >= 0) {
                      String successString = line.substring(0, indexSeparator).trim();
                      String fileString = line.substring(indexSeparator + 1).trim();
                      boolean successExpected = "provable".equals(successString);
                      File testFile = new File(exampleDir, fileString);
                      if (testFile.isFile()) {
                          result.add(new Object[] {testFile, defaultHeader, successExpected});
                      }
                   }
               }
           } 
           finally {
               if (reader != null) {
                   reader.close();
               }
           }
        }
        else {
           System.out.println("Skipping \"" + indexFile + "\" becaue it is no existing file.");
        }
        return result;
    }
}