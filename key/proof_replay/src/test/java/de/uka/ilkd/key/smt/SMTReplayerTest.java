package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import org.junit.Test;

import java.io.File;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.Collections;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class SMTReplayerTest {
    /*
    @Test
    public void testFindProofStart() throws URISyntaxException, IOException {
        for (int i = 0; i < paths.length; i++) {
            URL proofURL = SMTReplayer.class.getResource(paths[i]);
            System.out.println("Url is " + proofURL);

            Services services = new Services(JavaProfile.getDefaultProfile());
            InitConfig ic = new InitConfig(services);

            de.uka.ilkd.key.logic.Term problem = services.getTermBuilder().tt();
            Proof p = new Proof("test", problem, "", ic);

            String smtProof = new String(Files.readAllBytes(Paths.get(proofURL.toURI())));
            Goal goal = p.openGoals().head();
            SMTReplayer replayer = new SMTReplayer(smtProof, goal);

            replayer.replay();
            Proof proof = replayer.getProof();
            String proofStartName = replayer.getProofStart().rulename.getText();
            Assert.assertEquals(expProofStartNames[i], proofStartName);
        }
    }**/

    private Proof loadAndReplaySMT(File f) throws ProblemLoaderException {

        ProofManagementApi pmapi = KeYApi.loadFromKeyFile(f);
        ProofApi papi = pmapi.getLoadedProof();
        Proof proof = papi.getProof();

        SolverType z3Type = null;
        ProofIndependentSMTSettings pisettings = ProofIndependentSMTSettings.getDefaultSettingsData();
        for (SolverType type : pisettings.getSupportedSolvers()) {
            if (type.getName().equals("Z3_NEW_TL")) {
                z3Type = type;
                break;
            }
        }

        if (z3Type == null) {
            throw new IllegalStateException("Z3 solver is not available!");
        }

        final SolverType finalZ3Type = z3Type;

        de.uka.ilkd.key.settings.SMTSettings settings = new SMTSettings(proof.getSettings().getSMTSettings(),
            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(), proof);
        SolverLauncher launcher = new SolverLauncher(settings);
        final Proof[] result = {null};
        launcher.addListener(new SolverLauncherListener() {
            @Override
            public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers) {
                System.out.println("Z3 finished!");
                // only single solver started -> is expected to finish
                SMTSolver z3 = finishedSolvers.iterator().next();
                SMTReplayer replayer = new SMTReplayer(z3.getProblem());
                replayer.replay();
                result[0] = replayer.getProof();
            }

            @Override
            public void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes, SolverLauncher launcher) {
            }
        });
        launcher.launch(Collections.singleton(finalZ3Type),
            SMTProblem.createSMTProblems(proof),
            proof.getServices());
        return result[0];
    }

    /**
     * Tests if replay of the simple proof is successful.
     */
    @Test
    public void testSimpleProofReplay() throws Exception {
        File f = Paths.get(SMTReplayer.class.getResource("simple.key").toURI()).toFile();
        /* TODO: currently this proof can not be closed automatically (KeY's auto mode needed for
         *  th-lemma/asserted replay)
         */
        assertNotNull(loadAndReplaySMT(f));
    }

    /**
     * Tests if replay of the proof with annotations is successful.
     */
    //@Test
    public void testProofWithAnnotationsReplay() throws Exception {
        File f = Paths.get(SMTReplayer.class.getResource("annotation_test.key").toURI()).toFile();
        assertNotNull(loadAndReplaySMT(f));
    }

    /**
     * Tests if replay of the contraposition proof is successful.
     */
    @Test
    public void testContrapositionProofReplay() throws Exception {
        File f = Paths.get(SMTReplayer.class.getResource("contraposition.key").toURI()).toFile();
        assertTrue(loadAndReplaySMT(f).closed());
    }
}
