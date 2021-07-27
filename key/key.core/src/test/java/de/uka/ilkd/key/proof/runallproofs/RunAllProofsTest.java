// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.runallproofs;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionLexer;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionParser;
import org.antlr.runtime.*;
import org.junit.Test;
import org.junit.experimental.categories.Category;
import org.key_project.util.testcategories.Slow;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import static org.junit.Assert.assertTrue;

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
 * This class itself does not define testcases. The class has subclasses which
 * define test cases for different run-all-proof scenarios.
 *
 * @author Martin Hentschel
 * @see RunAllProofsTestSuite
 * @see ListRunAllProofsTestCases
 */
@Category(Slow.class)
public abstract class RunAllProofsTest {

   public static final String VERBOSE_OUTPUT_KEY = "verboseOutput";

   public static final String IGNORE_KEY = "ignore";

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
     * set of data. {@link Object#toString()} of first constructor parameter is
     * used to determine name of individual test cases, see {@link
     * RunAllProofsTestUnit#toString()} for further information.
     *
     * @param proofCollection
     *            The file name of the index file which parsed to produce test
     *            cases
     * @return The parameters. Each row will be one test case.
     * @throws IOException
     *             If an exceptions occurs while reading and parsing the index
     *             file
     */

   public static List<RunAllProofsTestUnit[]> data(ProofCollection proofCollection) throws IOException {

      /*
       * Create list of constructor parameters that will be returned by this
       * method. Suitable constructor is automatically determined by JUnit.
       */
      List<RunAllProofsTestUnit[]> data = new LinkedList<>();
      List<RunAllProofsTestUnit> units = proofCollection.createRunAllProofsTestUnits();
      for (RunAllProofsTestUnit unit : units) {
         data.add(new RunAllProofsTestUnit[] { unit });
      }

      return data;
   }

   /**
    * Uses {@link ProofCollectionParser} to parse the given file and returns a
    * parse result that is received from main parser entry point.
    */
   public static ProofCollection parseIndexFile(final String index) throws IOException {
      return parseIndexFile(index, new Function<TokenStream, ProofCollectionParser>() {
         @Override
         public ProofCollectionParser apply(TokenStream t) {
            return new ProofCollectionParser(t);
         }
      });
   }

   public static ProofCollection parseIndexFile(final String index,
            Function<TokenStream, ProofCollectionParser> stream2Parser) throws IOException {
      File automaticJAVADL = new File(RunAllProofsDirectories.EXAMPLE_DIR, index);
      CharStream charStream = new ANTLRFileStream(automaticJAVADL.getAbsolutePath());
      ProofCollectionLexer lexer = new ProofCollectionLexer(charStream);
      TokenStream tokenStream = new CommonTokenStream(lexer);
      ProofCollectionParser parser = stream2Parser.apply(tokenStream);
      try {
         return parser.parserEntryPoint();
      } catch (RecognitionException e) {
         String msg = parser.getErrorMessage(e, parser.getTokenNames());
         throw new IOException("Cannot parse " + automaticJAVADL +
                               " at line " + e.line + ": " + msg, e);
      }
   }
}
