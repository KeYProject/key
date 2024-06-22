/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import java.io.File;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.regex.Pattern;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.testgen.smt.testgen.TGPhase;
import de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLifecycleListener;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import picocli.CommandLine;

@CommandLine.Command(name = "tcgen", mixinStandardHelpOptions = true,
    description = "Generator of Testcases based on Proof Attempts")
public class TGMain implements Callable<Integer> {
    private static final Logger LOGGER = LoggerFactory.getLogger("main");

    public static void main(String[] args) {
        System.exit(mainwox(args));
    }

    /// main w/o System.exit
    public static int mainwox(String[] args) {
        return new CommandLine(new TGMain()).execute(args);
    }

    @CommandLine.Parameters(description = "KeY or Java file.", arity = "1..*")
    private List<Path> files = new LinkedList<>();

    @CommandLine.Option(names = "-T", description = "Number of parallel jobs", defaultValue = "4")
    private int numberOfThreads = 4;

    @CommandLine.Option(names = { "-s", "--symbex" },
        description = "apply symbolic execution", negatable = true)
    private boolean symbex;

    @CommandLine.Option(names = { "-c", "--contract" }, arity = "*",
        description = "name of the contract to be loaded in the Java environment. Can be a regular expression")
    private List<String> contractNames = new ArrayList<>();

    @CommandLine.Option(names = { "--all-contracts" },
        description = "test case generation for all contracts")
    private boolean allContracts = false;

    @CommandLine.Option(names = { "-o", "--output" }, description = "Output folder")
    private File outputFolder = new File("out");

    @CommandLine.Option(names = { "-r", "--rfl" }, description = "Use Reflection class",
        negatable = true)
    private boolean useReflection = false;

    @CommandLine.Option(names = { "--max-unwinds" }, description = "max unwinds of loops")
    private int maxUnwinds = 10;

    @CommandLine.Option(names = { "--dups" }, description = "remove duplicates", negatable = true)
    private boolean removeDuplicates;

    @CommandLine.Option(names = { "--only-tests" },
        description = "only put test classes directly in the output folder, no build file, no copy of sources",
        negatable = true)
    private boolean onlyTestClasses;


    @Override
    public Integer call() throws Exception {
        if (SolverTypes.Z3_CE_SOLVER.checkForSupport()) {
            LOGGER.error("Z3 not found! Bye.");
            return 1;
        } else {
            LOGGER.info("Z3 found; Version {}", SolverTypes.Z3_CE_SOLVER.getInstalledVersion());
        }

        var settings = new TestGenerationSettings();
        TestGenerationLifecycleListener log = new SysoutTestGenerationLifecycleListener();
        settings.setOutputPath(outputFolder.getAbsolutePath());
        settings.setUseRFL(useReflection);
        settings.setApplySymbolicExecution(symbex);
        settings.setMaxUnwinds(maxUnwinds);
        settings.setRemoveDuplicates(removeDuplicates);
        settings.setOnlyTestClasses(onlyTestClasses);

        var contractNameMatcher = Pattern.compile(String.join("|", contractNames))
                .asMatchPredicate();

        if (allContracts) {
            LOGGER.info("I accept every contract given by `--all-contracts`");
        } else if (contractNames.isEmpty()) {
            LOGGER.info(
                "Only printing the contracts. You need to give contracts with `-c` or use `--all-contracts`.");
        } else {
            LOGGER.info("Regex matching against contract names is: {}", contractNameMatcher);
        }


        for (Path file : files) {
            List<Proof> proofs = new LinkedList<>();
            var env = KeYEnvironment.load(file);
            Proof proof = env.getLoadedProof();
            if (proof == null) { // non-key file
                var print = !allContracts && contractNames.isEmpty();
                var contracts = env.getProofContracts();
                for (Contract contract : contracts) {
                    final var name = contract.getName();
                    if (print) {
                        LOGGER.info("Contract found: {}", name);
                    } else if (allContracts || contractNameMatcher.test(name)) {
                        var p =
                            env.createProof(contract.createProofObl(env.getInitConfig(), contract));
                        proofs.add(p);
                    }
                }
            } else { // key file
                proofs = List.of(proof);
            }

            LOGGER.info("Number of proof found: {}", proofs.size());

            final var maxThreads = Math.min(numberOfThreads, proofs.size());
            try (var exec = Executors.newFixedThreadPool(maxThreads)) {
                LOGGER.info("Start processing with {} threads", maxThreads);
                var tasks = proofs.stream().map(
                    p -> TestgenFacade.generateTestcasesTask(env, p, settings, log)).toList();
                var futures = tasks.stream().map(exec::submit).toList();
                for (Future<?> future : futures) {
                    future.get();
                }
            } finally {
                proofs.forEach(Proof::dispose);
                env.dispose();
            }
        }
        return 0;
    }
}


class SysoutTestGenerationLifecycleListener implements TestGenerationLifecycleListener {
    private static final Logger LOGGER = LoggerFactory.getLogger("main");

    @Override
    public void writeln(Object sender, @Nullable String message) {
        if (message != null) {
            LOGGER.info(message);
        }
    }

    @Override
    public void writeException(Object sender, Throwable throwable) {
        LOGGER.error("Error occurred!", throwable);
    }

    @Override
    public void finish(Object sender) {

    }

    @Override
    public void phase(Object sender, TGPhase phase) {

    }
}
