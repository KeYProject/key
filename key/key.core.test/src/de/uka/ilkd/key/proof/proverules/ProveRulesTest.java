package de.uka.ilkd.key.proof.proverules;

import static org.junit.Assert.*;

import java.io.File;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.LemmaJustification;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * JUnit test class for re-running taclet proofs (formerly implemented as Perl
 * script proveRules.pl).
 * 
 * @author Kai Wallisch
 *
 */
@RunWith(Parameterized.class)
public class ProveRulesTest {

   /*
    * File object pointing to directory key/key.core.test
    */
   private static final File KEY_CORE_TEST;
   private static final File PROOF_DIRECTORY;

   static {
      KEY_CORE_TEST = IOUtil.getProjectRoot(ProveRulesTest.class);
      PROOF_DIRECTORY = new File(KEY_CORE_TEST, "tacletProofs");
      assert PROOF_DIRECTORY.exists() : "Directory containing taclet proofs cannot be found at location: "
            + PROOF_DIRECTORY;
   }

   private final String tacletName;
   private final Taclet taclet;
   private final File proofFile;

   public ProveRulesTest(String tacletName,
         Map<String, Taclet> tacletObjectByTacletName,
         Map<String, File> proofFileByTacletName) {
      this.tacletName = tacletName;
      this.taclet = tacletObjectByTacletName.get(tacletName);
      this.proofFile = proofFileByTacletName.get(tacletName);
   }

   @Test
   public void loadTacletProof() {
      assertNotNull("Taclet " + tacletName
            + " was annoted with \\lemma but no taclet proof was found.",
            proofFile);
      assertNotNull("Proof file " + proofFile
            + " claims it has a proof for taclet " + tacletName
            + " but corresponding taclet seems to be unavailable.", taclet);
      assertTrue(
            "Found a taclet proof for taclet "
                  + tacletName
                  + " but the taclet is not registered as a lemma. It can be registered as a lemma by "
                  + "adding annotation \\lemma to the declaration of the taclet.",
            taclet.getRuleJustification() instanceof LemmaJustification);
      throw new UnsupportedOperationException();
   }

   private static List<File> getFilesRecursive(File directory) {
      assert directory.isDirectory() : "Expecting a directory as input parameter but found: "
            + directory;
      List<File> list = new LinkedList<>();
      for (File file : directory.listFiles()) {
         if (file.isFile()) {
            list.add(file);
         }
         else {
            list.addAll(getFilesRecursive(file));
         }
      }
      return list;
   }

   @Parameters(name = "{0}")
   public static Collection<Object[]> data() throws ProblemLoaderException {

      /*
       * Create a set containing names of taclets that shall be proven.
       */
      Set<String> tacletNames = new LinkedHashSet<>();

      /*
       * Add all annotated taclets to set of taclet names. Corresponding JUnit
       * test case of a taclet will fail if no proof file containg a taclet
       * proof for it can be found.
       */
      KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(
            null, null, null, null);
      Profile p = env.getProfile();
      Map<String, Taclet> tacletObjectByTacletName = new LinkedHashMap<>();
      for (Taclet taclet : env.getInitConfig().getTaclets()) {
         if (p.getJustification(taclet) == LemmaJustification.INSTANCE) {
            tacletNames.add(taclet.name().toString());
         }
      }

      /*
       * Traverse proof directory and add all taclets for which a proof file can
       * be found (proof of taclet "bsum_empty" is expected to be located in a
       * file named "Taclet_bsum_empty.proof"). Corresponding JUnit test will
       * fail if a proof for a taclet is present but taclet was not annotated
       * with "\lemma".
       */
      Map<String, File> proofFileByTacletName = new LinkedHashMap<>();
      List<File> proofFiles = getFilesRecursive(PROOF_DIRECTORY);
      for (File proofFile : proofFiles) {
         String tacletName = proofFile.getName();
         proofFileByTacletName.put(tacletName, proofFile);
         tacletNames.add(tacletName);
      }

      /*
       * Create list of constructor parameters containig one entry for each
       * taclet name. (that means there will be one test case for each taclet)
       */
      List<Object[]> result = new LinkedList<>();
      for (String tacletName : tacletNames) {
         result.add(new Object[] { tacletName, tacletObjectByTacletName,
               proofFileByTacletName });
      }
      return result;
   }

}
