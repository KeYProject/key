package org.key_project.key.cli;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptException;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.KeYConstants;
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

    @Option(names = {"--xml-output"}, description = "Output JUnit XML file")
    private File junitXmlOutput;

    @Option(names = {"--measuring"}, description = "Enable proof coverage measurement")
    private boolean enableMeasuring;

    @Option(names = {"--includes"}, description = "Additional KeY files to include")
    private List<String> includes = new ArrayList<>();

    @Option(names = {"--auto-mode-max-step"}, description = "Max steps in auto-mode", defaultValue = "10000")
    private int autoModeStep = 10000;

    @Option(names = {"-v", "--verbose"}, description = "Verbose output")
    private boolean verbose;

    @Option(names = {"-d", "--debug"}, description = "Debug output")
    private boolean debug;

    @Option(names = {"--read-contract-names-from-file"}, description = "Read contract names from proof file")
    private boolean readContractNames;

    @Option(names = {"--no-auto-mode"}, description = "Disable auto-mode fallback")
    private boolean disableAutoMode;

    @Option(names = {"--statistics"}, description = "Write proof statistics to JSON file")
    private File statisticsFile;

    @Option(names = {"--append-stat"}, description = "Append statistics to existing file")
    private boolean appendStatistics;

    @Option(names = {"--dry-run"}, description = "Skip proof execution")
    private boolean dryRun;

    @Option(names = {"--classpath", "-cp"}, description = "Additional classpaths")
    private List<String> classpath = new ArrayList<>();

    @Option(names = {"--bootClassPath", "-bcp"}, description = "Boot classpath")
    private String bootClassPath;

    @Option(names = {"--contract"}, description = "Include specific contract by name")
    private List<String> onlyContracts = new ArrayList<>();

    @Option(names = {"--forbid-contract"}, description = "Exclude specific contract by name")
    private List<String> forbidContracts = new ArrayList<>();

    @Parameters(index = "0..*", description = "Input KeY file or directory")
    private List<String> inputFile = new ArrayList<>();

    @Option(names = {"--proof-path"}, description = "Directory to search for proof files")
    private List<String> proofPath = new ArrayList<>();

    @Option(names = {"--default-script"}, description = "Default script file for fallback")
    private File defaultScript;

    private int errors = 0;
    private TestSuites testSuites = new TestSuites();

    public static void main(String[] args) {
        int exitCode = new CommandLine(new Main()).execute(args);
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
        for (String file : inputFile) {
            run(file);
        }

        // Write statistics if requested
        if (statisticsFile != null) {
            // Logic to write statistics (similar to Kotlin version)
        }

        // Write JUnit XML if requested
        if (junitXmlOutput != null) {
            try (var writer = java.nio.file.Files.newBufferedWriter(junitXmlOutput.toPath())) {
                testSuites.writeXml(writer);
            } catch (Exception e) {
                err("Failed to write XML: " + e.getMessage());
            }
        }

        System.exit(errors);
    }

    private void run(String inputFile) {
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

    private Path findProofFile(String contractName) {
        // Logic to find proof file (simplified)
        return null; // Placeholder
    }

    private Path findScriptFile(String filename) {
        // Logic to find script file (simplified)
        return null; // Placeholder
    }
}