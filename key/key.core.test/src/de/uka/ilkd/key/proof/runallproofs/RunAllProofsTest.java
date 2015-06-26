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

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;
import org.junit.AfterClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionLexer;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionParser;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.StatisticsFile;

/**
 * <p>
 * This class uses the provided example files from KeY for test purpose on the
 * same way as the bin/runAllProofs.pl does it.
 * </p>
 * 
 * <p>
 * RunAllProofs documentation can be found at the following location in KeY git
 * repository: key/doc/README.runAllProofs
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
public class RunAllProofsTest {
   /**
    * The path to the KeY repository. Configurable via system property
    * {@code key.home}.
    */
   public static final File KEY_HOME;

   public static final File EXAMPLE_DIR;

   public static final File KEY_CORE_TEST;

   private static StatisticsFile statisticsFile = null;

   public static final String VERBOSE_OUTPUT_KEY = "verboseOutput";

   public static final String IGNORE_KEY = "ignore";

   /**
    * Computes the constant values.
    */
   static {
      KEY_HOME = IOUtil.getProjectRoot(RunAllProofsTest.class).getParentFile();
      EXAMPLE_DIR = new File(KEY_HOME, "key.ui" + File.separator + "examples");
      KEY_CORE_TEST = new File(KEY_HOME, "key.core.test");
   }

   private static void assertDirectoryExists(File dir) {
      if (!dir.exists()) {
         throw new RuntimeException("Cannot run tests, directory " + dir
               + " does not exist.");
      }
   }

   private final RunAllProofsTestUnit unit;

   /**
    * Constructor.
    * 
    * @param unit
    *           {@link RunAllProofsTestUnit} whose test will be executed.
    */
   public RunAllProofsTest(RunAllProofsTestUnit unit) {
      this.unit = unit;
   }

   /**
    * Tests each file defined by the instance variables. The tests steps are
    * described in the constructor of this class.
    * 
    * @throws Exception
    */
   @Test
   public void testWithKeYAutoMode() throws Exception {
      TestResult report = unit.runTest();
      assertTrue(report.message, report.success);
   }

   /**
    * Creates a set of constructor parameters for this class. Uses JUnits
    * parameterized test case mechanism for to create several test cases from a
    * set of data. {@link Object.#toString()} of first constructor parameter is
    * used to determine name of individual test cases, see {@link
    * RunAllProofsTestUnit.#toString()} for further information.
    * 
    * @return The parameters. Each row will be one test case.
    * @throws IOException
    *            Occurred Exception.
    * @throws RecognitionException
    */
   @Parameters(name = "{0}")
   public static Collection<Object[]> data() throws IOException,
         RecognitionException {
      assertDirectoryExists(KEY_HOME);
      assertDirectoryExists(KEY_CORE_TEST);
      assertDirectoryExists(EXAMPLE_DIR);

      /*
       * Parse index file containing declarations for KeY files that will be
       * verified.
       */
      ProofCollection proofCollection = parseIndexFile();

      /*
       * Set up statistics file.
       */
      statisticsFile = proofCollection.getSettings().getStatisticsFile();
      statisticsFile.setUp();

      /*
       * Create list of constructor parameters that will be returned by this
       * method. Suitable constructor is automatically determined by JUnit.
       */
      Collection<Object[]> data = new LinkedList<Object[]>();
      List<RunAllProofsTestUnit> units = proofCollection
            .createRunAllProofsTestUnits();
      for (RunAllProofsTestUnit unit : units) {
         data.add(new RunAllProofsTestUnit[] { unit });
      }
      return data;
   }

   @AfterClass
   public static void computeSumsAndAverages() throws IOException {
      statisticsFile.computeSumsAndAverages();
   }

   /**
    * Uses {@link ProofCollectionParser} to parse the given file and returns a
    * parse result that is received from main parser entry point.
    */
   public static ProofCollection parseIndexFile() throws IOException,
         RecognitionException {
      File automaticJAVADL = new File(EXAMPLE_DIR, "index/automaticJAVADL.txt");
      CharStream charStream = new ANTLRFileStream(
            automaticJAVADL.getAbsolutePath());
      ProofCollectionLexer lexer = new ProofCollectionLexer(charStream);
      TokenStream tokenStream = new CommonTokenStream(lexer);
      ProofCollectionParser parser = new ProofCollectionParser(tokenStream);
      return parser.parserEntryPoint();
   }
}
