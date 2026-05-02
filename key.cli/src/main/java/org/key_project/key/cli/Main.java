package org.key_project.key.cli;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptException;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.KeYConstants;
import org.jspecify.annotations.Nullable;
import picocli.CommandLine;
import picocli.CommandLine.Command;
import picocli.CommandLine.Option;
import picocli.CommandLine.Parameters;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import static org.key_project.key.cli.Ansi.*;

@Command(name = "key-checker", description = "A tool for checking KeY proofs.")
public class Main implements Runnable {
    @Option(names = {"--color"}, description = "Color output mode: YES, NO, AUTO")
    private String color = "AUTO";

    @Option(names = {"--auto-mode-max-step"}, description = "Max steps in auto-mode", defaultValue = "10000")
    private int autoModeStep = 10000;

    @Option(names = {"-v", "--verbose"}, description = "Verbose output")
    private boolean verbose;

    @Option(names = {"--statistics"}, description = "Write proof statistics to JSON file")
    private File statisticsFile;

    @Option(names = {"--append-stat"}, description = "Append statistics to existing file")
    private boolean appendStatistics;

    @Option(names = {"--dry-run"}, description = "Skip proof execution")
    private boolean dryRun;

    @Option(names = {"--classpath", "-cp"}, description = "Additional classpaths")
    private List<Path> classpath = new ArrayList<>();

    @Option(names = {"--bootClassPath", "-bcp"}, description = "Boot classpath")
    private @Nullable Path bootClassPath;

    @Option(names = {"--includes"}, description = "Additional KeY files to include")
    private List<Path> includes = new ArrayList<>();

    @Option(names = {"--contract"}, description = "Include specific contract by name")
    private List<String> onlyContracts = new ArrayList<>();

    @Parameters(index = "0..*", description = "Input KeY file or directory")
    private List<Path> inputFile = new ArrayList<>();

    @Option(names = "--show-properties", description = "list all Java properties and exit")
    private boolean showProperties = false;

    @Option(names = {"--script", "-s"}, description = "Include specific contract by name")
    private @Nullable String script = null;

    @Option(names = {"--script-path", "-sp"}, description = "Include specific contract by name")
    private @Nullable Path scriptPath = null;


    /**
     * This parameter disables the possibility to prune in
     * closed branches. It is meant as a fallback solution
     * if storing all closed goals needs too much memory.
     */
    @Option(names = "--no-pruning-closed",
            description = "disables pruning and goal back in closed branches (saves memory)")
    private boolean isNoPruningClosed = true;

    /**
     * If this option is set, the (Disk)FileRepo does not delete its temporary
     * directories (can be
     * used for debugging).
     */
    @Option(names = "--keep-fileRepos",
            description = "disables the automatic deletion of temporary"
                    + "directories of file repos (for debugging)")
    private boolean isKeepFileRepos = false;


    @Option(names = "--timeout", paramLabel = "INT",
            description = "timeout for each automatic proof of a problem in ms (default: "
                    + LemmataAutoModeOptions.DEFAULT_TIMEOUT + ", i.e., no timeout)")
    private int timeout = -1;


    @CommandLine.ArgGroup(
            heading = "Options for justify rules. autoprove taclets (options always with prefix --jr) needs the path to the rule file as argument       The JUSTIFY_RULES option has a number of additional parameters you can set. The following options only apply if --jr-enable is used.")
    private @Nullable LemmataAutoModeOptions justifyRulesOptions;


    public static void main(String[] args) {
        int exitCode = new CommandLine(new Main())
                .setAbbreviatedSubcommandsAllowed(true)
                .execute(args);
        System.exit(exitCode);
    }

    @Override
    public void run() {
        // Set color mode
        useColor = "YES".equals(color) || ("AUTO".equals(color) && System.console() != null);

        // Print KeY version info
        printm("KeY version: " + KeYConstants.VERSION);
        printm("KeY internal: " + KeYConstants.INTERNAL_VERSION);
        printm("Copyright: " + KeYConstants.COPYRIGHT);

        // Process each input file
        for (Path file : inputFile) {
            run(file);
        }

        // Write statistics if requested
        if (statisticsFile != null) {
            // Logic to write statistics (similar to Kotlin version)
        }

        System.exit(errors);
    }

    private void run(Path inputFile) {
        info("Start with `" + inputFile + "`");
        currentPrintLevel++;
        // Load KeY environment
        try (KeYEnvironment<?> pm = KeYEnvironment.load(
                Paths.get(inputFile),
                classpath.stream().map(Paths::get).toList(),
                bootClassPath != null ? Paths.get(bootClassPath) : null,
                includes.stream().map(Paths::get).toList())) {

            List<Contract> contracts = pm.getProofContracts().stream()
                    .filter(c -> onlyContracts.isEmpty() || onlyContracts.contains(c.getName()))
                    .toList();

            info("Found: " + contracts.size());

            int successful = 0, ignored = 0, failure = 0, error = 0;
            TestSuite testSuite = testSuites.newTestSuite(inputFile);

            for (Contract c : contracts) {
                TestCase testCase = testSuite.newTestCase(c.getName());
                info("[INFO] Contract: `" + c.getName() + "`");
                currentPrintLevel++;
                if (forbidContracts.contains(c.getName())) {
                    printm(" [INFO] Contract excluded by `--forbid-contract`");
                    testCase.result = new TestCaseKind.Skipped("Contract excluded by `--forbid-contract`.");
                    ignored++;
                } else if (dryRun) {
                    printm("[INFO] Contract skipped by `--dry-run`");
                    testCase.result = new TestCaseKind.Skipped("Contract skipped by `--dry-run`.");
                    ignored++;
                } else {
                    ProofState state = runContract(pm, c);
                    switch (state) {
                        case Success:
                            successful++;
                            break;
                        case Failed:
                            testCase.result = new TestCaseKind.Failure("Proof not closeable.", "failure");
                            failure++;
                            break;
                        case Skipped:
                            ignored++;
                            break;
                        case Error:
                            error++;
                            break;
                    }
                }
                currentPrintLevel--;
            }

            printm("[INFO] Summary for " + inputFile + ": (successful/ignored/failure) (" +
                    colorfg(successful, GREEN) + "/" +
                    colorfg(ignored, BLUE) + "/" +
                    colorfg(failure, RED) + ")");

            if (failure != 0) {
                err(inputFile + " failed!");
            }
            currentPrintLevel--;
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private ProofState runContract(KeYEnvironment<?> pm, Contract contract) throws Exception {
        Proof proof = pm.createProof(contract.createProofObl(pm.getInitConfig()));
        if (proof == null) {
            fail("No proof created for contract: " + contract.getName());
            return ProofState.Error;
        }

        proof.getSettings().getStrategySettings().setMaxSteps(autoModeStep);
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(autoModeStep);

        Path proofFile = findProofFile(contract.getName());
        Path scriptFile = findScriptFile(contract.getName());

        AbstractUserInterfaceControl ui = (AbstractUserInterfaceControl) pm.getUi();
        AbstractProofControl pc = (AbstractProofControl) pm.getProofControl();

        ProofState closed;
        if (proofFile != null) {
            info("Proof found: " + proofFile + ". Try loading.");
            closed = loadProof(proofFile);
        } else if (scriptFile != null) {
            info("Script found: " + scriptFile + ". Try proving.");
            closed = loadScript(ui, proof, scriptFile);
        } else {
            if (verbose) {
                info("No proof or script found. Fallback to auto-mode.");
            }
            if (disableAutoMode) {
                warn("Proof skipped because `--no-auto-mode` switch is set.");
                closed = ProofState.Skipped;
            } else {
                closed = runDefaultFallback(ui, pc, proof);
            }
        }

        switch (closed) {
            case Success:
                fine("✔ Proof closed.");
                break;
            case Skipped:
                warn("! Proof skipped.");
                break;
            case Failed:
                errors++;
                err("✘ Proof open.");
                debug(proof.openGoals().size() + " remains open");
                break;
            case Error:
                fail("Could not load proof due to exception in KeY.");
                break;
        }

        proof.dispose();
        return closed;
    }

    private ProofState runDefaultFallback(AbstractUserInterfaceControl ui, AbstractProofControl pc, Proof proof) throws ScriptException, IOException, InterruptedException {
        if (defaultScript != null) {
            info("Using default script for fallback: " + defaultScript + ". Try proving.");
            return loadScript(ui, proof, defaultScript.toPath());
        } else {
            return runAutoMode(pc, proof);
        }
    }

    private ProofState runAutoMode(AbstractProofControl proofControl, Proof proof) {
        long time = System.currentTimeMillis();
        try {
            if (enableMeasuring) {
                MeasuringMacro mm = new MeasuringMacro();
                proofControl.runMacro(proof.root(), mm, null);
                proofControl.waitWhileAutoMode();
                info("Proof has open/closed before: " + mm.before);
                info("Proof has open/closed after: " + mm.after);
            } else {
                proofControl.startAndWaitForAutoMode(proof);
            }
        } catch (Exception e) {
            fail("Error in KeY during auto mode. " + e.getClass() + " : " + e.getMessage());
            return ProofState.Error;
        }
        time = System.currentTimeMillis() - time;

        if (verbose) {
            fine("Auto-mode took " + (time / 1000.0) + " seconds.");
        }

        printStatistics(proof);
        return proof.closed() ? ProofState.Success : ProofState.Failed;
    }

    private ProofState loadScript(AbstractUserInterfaceControl ui, Proof proof, Path scriptFile) throws IOException, ScriptException, InterruptedException {
        ProofScriptEngine engine = new ProofScriptEngine(ParsingFacade.parseScript(scriptFile));
        engine.execute(ui, proof);

        // Placeholder for actual script execution
        try {
            // Simulate script execution
            Thread.sleep(1000); // Simulate time
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return ProofState.Error;
        }

        printStatistics(proof);
        return proof.closed() ? ProofState.Success : ProofState.Failed;
    }

    private ProofState loadProof(Path proofFile) throws Exception {
        try (KeYEnvironment<?> env = KeYEnvironment.load(proofFile)) {
            Proof proof = env.getLoadedProof();

            if (proof.closed()) {
                return ProofState.Success;
            } else {
                return ProofState.Failed;
            }
        }
    }

    private void printStatistics(Proof proof) {
        // Print statistics (simplified)
        if (statisticsFile != null) {
            // Logic to write statistics
        }
        if (verbose) {
            proof.getStatistics().getSummary().forEach((p) -> debug(p.first + " = " + p.second));
        }
        if (enableMeasuring) {
            // Logic to print visited lines
        }
    }
}