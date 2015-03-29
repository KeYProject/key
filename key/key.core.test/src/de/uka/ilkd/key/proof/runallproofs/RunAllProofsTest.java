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

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.Parameterized;

import de.uka.ilkd.key.proof.runallproofs.ProofCollectionParser.parserEntryPoint_return;

import org.key_project.util.java.IOUtil;
import static org.junit.Assert.*;

/**
 * <p>
 * This class uses the provided example files from KeY for test purpose on the
 * same way as the bin/runAllProofs.pl does it.
 * </p>
 * 
 * <p>
 * The files to test are listed in: <br />
 * $KEY_HOME/key.core.test/resources/testcase/runallproofs/automaticJAVADL.txt <br />
 * The paths specified in this file are treated relative to path $KEY_HOME/key.ui/examples
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
     * The path to the KeY repository. 
     * Configurable via system property {@code key.home}.
     */
    private static final String KEY_HOME;
    
    static final File EXAMPLE_DIR;
    
    /**
     * Computes the constant values.
     */
    static {
        KEY_HOME = System.getenv("KEY_HOME");
        if (KEY_HOME == null) {
            throw new RuntimeException("Environment variable KEY_HOME not set. "
                    + "Cannot test proofs.");
        }
        
        EXAMPLE_DIR = new File(KEY_HOME, "key.ui" + File.separator + "examples");
    }
    
    private final String defaultHeader;
    private final ProofCollectionUnit unit;

    /**
     * Constructor.
     * @param testFile The current file to test.
     * @param defaultHeader The default header to use.
     * @param successExpected The expected result.
     */
    public RunAllProofsTest(ProofCollectionUnit unit, String defaultHeader, Map<String, Object> settings) {
       this.unit = unit;
       this.defaultHeader = defaultHeader;
    }

    /**
     * Tests each file defined by the instance variables. The tests steps
     * are described in the constructor of this class.
     * @throws Exception
     */
   @Test
   public void testWithKeYAutoMode() throws Exception {
      File tmpFolder = new File(KEY_HOME + File.separator + "key.core.test" + File.separator + "tmp_runallproofs");
      if(!tmpFolder.exists()){
         System.out.println("Creating directory for temporary files: " + tmpFolder);
         Files.createDirectory(tmpFolder.toPath());
         tmpFolder.deleteOnExit();
      }
      Path tmpFile = Files.createTempFile(tmpFolder.toPath(), null, null);
      tmpFile.toFile().deleteOnExit(); // deletes the temporary file when JVM terminates
      Files.write(tmpFile, convertToByteArray(unit));
      ProcessBuilder pb = new ProcessBuilder("java", "-classpath",
            System.getProperty("java.class.path"),
            this.getClass().getName(),
            tmpFile.toString());
//      System.out.println("Starting process: " + pb.command());
      Process process = pb.inheritIO().start();
      process.waitFor();
      assertEquals("Executed process terminated with non-zero exit value.", process.exitValue(),0);
   }
    
   private static Object convertToObject(byte[] bytes) throws IOException, ClassNotFoundException {
      ByteArrayInputStream byteArrayInputStream = new ByteArrayInputStream(bytes);
      ObjectInputStream objectInputStream = new ObjectInputStream(byteArrayInputStream);
      return objectInputStream.readObject();
   }

    private static byte[] convertToByteArray(Serializable o) throws IOException {
       ByteArrayOutputStream byteArrayOutputStream = new ByteArrayOutputStream();
       ObjectOutputStream objectOutputStream = new ObjectOutputStream(byteArrayOutputStream);
       objectOutputStream.writeObject(o);
       objectOutputStream.flush();
       return byteArrayOutputStream.toByteArray();
    }
    
    public static void main(String[] args) throws Exception{
        ProofCollectionUnit unit = (ProofCollectionUnit)convertToObject(Files.readAllBytes(new File(args[0]).toPath()));
        unit.processProofObligations();
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
     * Collects all test files. Instances of this class are automatically
     * created with the returned parameters by the JUnit test suite
     * {@link CustomParameters}.
     * @return The parameters. Each row will be one test case.
     * @throws IOException Occurred Exception.
    * @throws RecognitionException 
     */
    @Parameters
    public static Collection<Object[]> data() throws IOException, RecognitionException {
        
        // Read default header
        String defaultHeader = IOUtil.readFrom(new FileInputStream(new File(EXAMPLE_DIR, "index/headerJavaDL.txt")));
        
        // parse index file containing declarations for proof obligations
        File automaticJAVADL = new File(EXAMPLE_DIR, "index/automaticJAVADL_new.txt");
        parserEntryPoint_return parseResult= parseFile(automaticJAVADL);
        
        Map<String, Object> settings = getSettings();
        
        // create list of constructor parameters that will be returned by this method
        Collection<Object[]> data = new LinkedList<Object[]>();
        for(ProofCollectionUnit unit : parseResult.units){
           data.add(new Object[]{unit, defaultHeader, settings});
        }
        return data;
    }
    
    private static Map<String, Object> getSettings() {
      Map<String, Object> ret = new HashMap<>();
      return ret;
   }

   private static parserEntryPoint_return parseFile(File file) throws IOException, RecognitionException {
       CharStream charStream = new ANTLRStringStream(IOUtil.readFrom(file));
       ProofCollectionLexer lexer = new ProofCollectionLexer(charStream);
       TokenStream tokenStream = new CommonTokenStream(lexer);
       ProofCollectionParser parser = new ProofCollectionParser(tokenStream);
       return parser.parserEntryPoint();
   }
}
