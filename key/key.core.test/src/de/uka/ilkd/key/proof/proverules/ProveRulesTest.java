package de.uka.ilkd.key.proof.proverules;

import java.io.File;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

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
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.rule.Taclet;

@RunWith(Parameterized.class)
public class ProveRulesTest {

   private static final File KEY_CORE_TEST = IOUtil
         .getProjectRoot(RunAllProofsTest.class);

   private final Taclet taclet;

   public ProveRulesTest(Taclet taclet) {
      this.taclet = taclet;
   }

   @Test
   public void loadTacletProof() {
       throw new UnsupportedOperationException();
   }

   @Parameters(name = "{0}")
   public static Collection<Object[]> data() throws ProblemLoaderException {
      List<Object[]> result = new LinkedList<>();
      KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(
            null, null, null, null);
      Profile p = env.getProfile();
      for (Taclet taclet : env.getInitConfig().getTaclets()) {
         if (p.getJustification(taclet) == LemmaJustification.INSTANCE) {
            result.add(new Object[] { taclet });
         }
      }
      return result;
   }

}
