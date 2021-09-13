package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;
import org.junit.Test;

import java.io.File;

public class ContractLoadingTests {
    public static final File EXAMPLES_DIR = new File("../key.ui/examples/");
    @Test public void sumAndMax() throws ProblemLoaderException {
        final File javaFile = new File(EXAMPLES_DIR, "heap/vstte10_01_SumAndMax/src/SumAndMax.java");
        ProofManagementApi file = KeYApi.loadProof(javaFile);
        Services services = file.getServices();
        for (Contract proofContract : file.getProofContracts()) {
            System.out.println(proofContract.getPlainText(services));
        }
    }
}
