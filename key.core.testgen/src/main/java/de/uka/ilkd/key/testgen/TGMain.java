/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.testgen.settings.TestGenerationSettings;
import de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLogger;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import picocli.CommandLine;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.Callable;

@CommandLine.Command(name = "tcgen", mixinStandardHelpOptions = true,
        description = "Generator of Testcases based on Proof Attempts")
public class TGMain implements Callable<Integer> {
    private final static Logger LOGGER = LoggerFactory.getLogger("main");

    public static void main(String[] args) throws ProblemLoaderException, InterruptedException {
        int exitCode = new CommandLine(new TGMain()).execute(args);
        System.exit(exitCode);
    }

    @CommandLine.Parameters(description = "KeY or Java file.", arity = "1..*")
    private List<File> files = new LinkedList<>();

    @CommandLine.Option(names = {"-s", "--symbex"},
            description = "apply symbex", negatable = true)
    private boolean symbex;

    @CommandLine.Option(names = {"-c", "--contract"},
            arity = "*",
            description = "name of the contract to be loaded in the Java environment")
    private List<String> contractNames = new ArrayList<>();

    @CommandLine.Option(names = {"--all-contracts"},
            description = "name of the contract to be loaded in the Java environment")
    private boolean allContracts = false;


    @CommandLine.Option(names = {"-o", "--output"}, description = "Output folder")
    private File outputFolder = new File("out");

    @CommandLine.Option(names = {"-r", "--rfl"}, description = "Use Reflection class", negatable = true)
    private boolean useReflection = false;

    @CommandLine.Option(names = {"-f", "--format"}, description = "Use Reflection class")
    private Format format = Format.JUnit4;


    @CommandLine.Option(names = {"--max-unwinds"}, description = "max unwinds")
    private int maxUnwinds = 10;
    @CommandLine.Option(names = {"--dups"}, description = "remove duplicates", negatable = true)
    private boolean removeDuplicates;

    @Override
    public Integer call() throws Exception {
        if (SolverTypes.Z3_CE_SOLVER.checkForSupport()) {
            LOGGER.error("Z3 not found! Bye.");
            return 1;
        } else {
            LOGGER.info("Z3 found; Version {}", SolverTypes.Z3_CE_SOLVER.getInstalledVersion());
        }

        var settings = new TestGenerationSettings();
        TestGenerationLogger log = new SysoutTestGenerationLogger();
        settings.setOutputPath(outputFolder.getAbsolutePath());
        settings.setRFL(useReflection);
        settings.setFormat(format);
        settings.setApplySymbolicExecution(symbex);
        settings.setMaxUnwinds(maxUnwinds);
        settings.setRemoveDuplicates(removeDuplicates);

        for (File file : files) {
            List<Proof> proofs = new LinkedList<>();
            var env = KeYEnvironment.load(file);
            Proof proof = env.getLoadedProof();
            if (proof == null) { // non-key file
                var print = contractNames.isEmpty();
                final var api = new ProofManagementApi(env);
                var contracts = api.getProofContracts();
                for (Contract contract : contracts) {
                    final var name = contract.getName();
                    if (print) {
                        LOGGER.info("Contract found: {}", name);
                    }

                    if (allContracts || contractNames.contains(name)) {
                        proofs.add(api.startProof(contract).getProof());
                    }
                }
            } else { // key file
                proofs = List.of(proof);
            }

            for (Proof p : proofs) {
                TestgenFacade.generateTestcases(env, p, settings, log);
                p.dispose();
            }

            env.dispose();
        }
        return 0;
    }

    private static class SysoutTestGenerationLogger implements TestGenerationLogger {
        @Override
        public void writeln(String message) {
            LOGGER.info(message);
        }

        @Override
        public void writeException(Throwable throwable) {
            LOGGER.error("Error occurred!", throwable);
        }

        @Override
        public void close() {
        }
    }
}
