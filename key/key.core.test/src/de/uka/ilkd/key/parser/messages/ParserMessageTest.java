package de.uka.ilkd.key.parser.messages;

import static org.junit.Assert.*;

import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.ExceptionTools;

/**
 * Parameterized JUnit test suite for testing parser messages. For
 * documentation, see: key/doc/README.parserMessageTest
 * 
 * @author Kai Wallisch
 *
 */
@RunWith(Parameterized.class)
public class ParserMessageTest {

   private static final File KEY_CORE_TEST = IOUtil
         .getProjectRoot(ParserMessageTest.class);

   private final String docFile = "key/doc/README.parserMessageTest";

   private final File sourceDir;

   public ParserMessageTest(String testName, File sourceDir) {
      this.sourceDir = sourceDir;
   }

   @Test
   public void verifyParserMessage() throws IOException {
      // retrieve the Java file contained in the given source directory:
      File javaFile = null;
      for (File file : sourceDir.listFiles()) {
         if (file.getName().endsWith(".java")) {
            assertEquals("Found multiple Java files in directory " + sourceDir
                  + "\nCannot unambiguously determine Java source file.", null,
                  javaFile);
            javaFile = file;
         }
      }
      assertNotEquals("No Java file found in directory " + sourceDir, null,
            javaFile);

      /*
       * Retrieve information about expected parser message from given Java
       * source file.
       */
      List<String> lines = Files.readAllLines(javaFile.toPath(),
            Charset.defaultCharset());
      assertTrue("Number of lines in file " + javaFile
            + " is less than required minimal number of lines."
            + "\nFirst three lines of tested Java source file must contain "
            + "information about expected parser message. " + "See file "
            + docFile + " for more information.", lines.size() >= 3);

      String firstLine = lines.get(0);
      String secondLine = lines.get(1);
      String thirdLine = lines.get(2);
      String errorMessage = "";
      if (!firstLine.startsWith("//MSG ")) {
         errorMessage += "First line of file " + javaFile
               + " must start with \"//MSG *regexp*\", "
               + "to specify a regular expression for the "
               + "expected parser message.";
      }
      if (!secondLine.startsWith("//LINE ")) {
         errorMessage += errorMessage.length() > 0 ? "\n" : "";
         errorMessage += "Second line of file " + javaFile
               + " must start with \"//LINE *number*\", "
               + "to specify the line number in which a parser error is "
               + "expected to occur.";
      }
      if (!thirdLine.startsWith("//COL ")) {
         errorMessage += errorMessage.length() > 0 ? "\n" : "";
         errorMessage += "Third line of file " + javaFile
               + " must start with \"//COL *number*\", "
               + "to specify the column number in which a parser error is "
               + "expected to occur.";
      }
      assertTrue(errorMessage + "\nSee file " + docFile
            + " for more information.", errorMessage.length() == 0);

      String parserMessageRegExp = firstLine.substring(6);
      int expectedLineNumber = Integer.parseInt(secondLine.substring(7));
      int expectedColumnNumber = Integer.parseInt(thirdLine.substring(6));

      ProblemLoaderException pe = null;
      try {
         KeYEnvironment.load(javaFile);
      }
      catch (ProblemLoaderException e) {
         pe = e;
      }
      assertNotEquals("Parsing unexpectedly did not throw a "
            + "ProblemLoaderException for file " + javaFile, null, pe);

      Location location = ExceptionTools.getLocation(pe);

      assertTrue("Couldn't recreate filename from received exception.",
            location.getFilename() != null
                  && location.getFilename().length() > 0);

      assertEquals("Filename retrieved from parser message "
            + "doesn't match filename of originally parsed file.", javaFile,
            new File(location.getFilename()));

      assertEquals("Line number of retrieved parser message "
            + "doesn't match expected line number.", expectedLineNumber,
            location.getLine());

      assertEquals("Column number of retrieved parser message "
            + "doesn't match expected column number.", expectedColumnNumber,
            location.getColumn());

      assertTrue(
            "Message of ProblemLoaderException doesn't match regular expression, "
                  + "that was specified in file " + javaFile
                  + "\nRequested regular expression: " + parserMessageRegExp
                  + "\nRetrieved exception message: " + pe.getMessage(), pe
                  .getMessage().matches(".*" + parserMessageRegExp + ".*"));
   }

   @Parameters(name = "{0}")
   public static Collection<Object[]> data() {
      File testDataDir = new File(KEY_CORE_TEST, "resources" + File.separator
            + "testcase" + File.separator + "parserMessageTest");
      Collection<Object[]> data = new LinkedList<>();
      for (File file : testDataDir.listFiles()) {
         if (file.isDirectory()) {
            data.add(new Object[] { file.getName(), file });
         }
      }
      return data;
   }
}
