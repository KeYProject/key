package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;
import org.junit.jupiter.api.Test;

import java.io.File;

/**
 * @author Alexander Weigl
 * @version 1 (31.01.25)
 */
public class Issue3452 {
    @Test
    void test() throws ProblemLoaderException, ProofInputException {
        final var input = new File("src/test/resources/de/uka/ilkd/key/nparser/Issue3452Fixture.java");
        var env
                = KeYEnvironment.load(input, null, null, null);
        final var contract = env.getProofContracts().getFirst();
        var po = contract.createProofObl(env.getInitConfig(), contract);
        env.createProof(po);
    }
}