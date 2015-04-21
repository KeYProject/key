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

package de.uka.ilkd.key.proof.runallproofs;

import static org.junit.Assert.*;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit.TestResult;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionLexer;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionParser;
import de.uka.ilkd.key.util.removegenerics.Main;

/**
 * <p>
 * This class uses the provided example files from KeY for test purpose on the
 * same way as the bin/runAllProofs.pl does it.
 * </p>
 * 
 * <p>
 * The files to test are listed in: <br />
 * $KEY_HOME/key.core.test/resources/testcase/runallproofs/automaticJAVADL.txt
 * </p>
 * 
 * <p>
 * The test steps for each defined test file are:
 * <ol>
 * <li>Create a copy with extension ".auto.key". The file contains the default
 * settings from examples/index/headerJavaDL.txt if required.</li>
 * <li>A new Java process is started for each test file. It executes
 * {@link Main#main(String[])} with the file as parameter and additional
 * parameter {@code auto}.</li>
 * <li>The process termination result must be {@code 0} if the proof is closed
 * and something different otherwise. This value is used to determine the test
 * result.</li>
 * </ol>
 * </p>
 * <p>
 * This class can be executed as "JUnit plug-in test" without extra
 * configurations. For execution as normal "Junit test" it is required to define
 * the system properties "key.home" and "key.lib" like:
 * {@code "-Dkey.home=D:/Forschung/GIT/KeY" "-Dkey.lib=D:/Forschung/Tools/KeY-External Libs"}
 * .
 * </p>
 * 
 * @author Martin Hentschel
 */
@RunWith(Parameterized.class)
public class RunAllProofsTest implements Serializable {
    /**
     * The path to the KeY repository. 
     * Configurable via system property {@code key.home}.
     */
    public static final File KEY_HOME;
    
    public static final File EXAMPLE_DIR;
    
    public static final File KEY_CORE_TEST;
    
    /**
     * Computes the constant values.
     */
    static {
        String keyHome = System.getenv("KEY_HOME");
        if (keyHome == null) {
            throw new RuntimeException("Environment variable KEY_HOME not set. "
                    + "Cannot test proofs.");
        }
        
        KEY_HOME = new File(keyHome);
        EXAMPLE_DIR = new File(KEY_HOME, "key.ui" + File.separator + "examples");
        KEY_CORE_TEST = new File(KEY_HOME, "key.core.test");
    }
    
   private static void assertDirectoryExists(File dir) {
      if (!dir.exists()) {
         throw new RuntimeException("Cannot run tests, directory " + dir + " does not exist.");
      }
   }
    
    final RunAllProofsTestUnit unit;

    /**
     * Constructor.
     * @param unit {@link RunAllProofsTestUnit} whose test will be executed.
     */
    public RunAllProofsTest(RunAllProofsTestUnit unit) {
       this.unit = unit;
    }

    /**
     * Tests each file defined by the instance variables. The tests steps
     * are described in the constructor of this class.
     * @throws Exception
     */
   @Test
   public void testWithKeYAutoMode() throws Exception {
      // ProofCollectionSubProcess.executeRunAllProofsTest(this);
      TestResult report = unit.runTest();
//      System.out.println(report.message);
//      System.gc(); System.out.println("Memory " + Runtime.getRuntime().totalMemory());
//      System.out.println("Time " + System.currentTimeMillis());
      assertTrue(report.message, report.success);
   }
    
    /**
     * Collects all test files. Instances of this class are automatically
     * created with the returned parameters by the JUnit test suite
     * {@link CustomParameters}.
     * @return The parameters. Each row will be one test case.
     * @throws IOException Occurred Exception.
    * @throws RecognitionException 
     */
   @Parameters
   public static Collection<Object[]> data() throws IOException,
         RecognitionException {
      assertDirectoryExists(KEY_HOME);
      assertDirectoryExists(KEY_CORE_TEST);
      assertDirectoryExists(EXAMPLE_DIR);

      /*
       * Parse index file containing declarations for proof obligations.
       */
      File automaticJAVADL = new File(EXAMPLE_DIR,
            "index/automaticJAVADL.txt");
      List<RunAllProofsTestUnit> units = parseFile(automaticJAVADL);

      /*
       * Create list of constructor parameters that will be returned by this method.
       * Suitable constructor is automatically determined by JUnit.
       */
      Collection<Object[]> data = new LinkedList<Object[]>();
      for (RunAllProofsTestUnit unit : units) {
         data.add(new Object[] { unit });
      }
      return data;
   }

   /**
    * Uses {@link ProofCollectionParser} to parse the given file and returns a
    * parse result that is received from main parser entry point.
    */
   private static List<RunAllProofsTestUnit> parseFile(File file)
         throws IOException, RecognitionException {
      CharStream charStream = new ANTLRFileStream(file.getAbsolutePath());
      ProofCollectionLexer lexer = new ProofCollectionLexer(charStream);
      TokenStream tokenStream = new CommonTokenStream(lexer);
      ProofCollectionParser parser = new ProofCollectionParser(tokenStream);
      return parser.parserEntryPoint();
   }
}
