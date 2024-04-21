package evaluation;

import com.google.common.util.concurrent.SimpleTimeLimiter;
import com.google.common.util.concurrent.TimeLimiter;
import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.isabelletranslation.IllegalFormulaException;
import de.uka.ilkd.key.gui.isabelletranslation.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.FullPropositionalExpansionMacro;
import de.uka.ilkd.key.macros.SMTPreparationMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import org.key_project.util.collection.ImmutableList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;
import java.util.stream.Stream;

import static java.nio.file.StandardOpenOption.APPEND;

public class Main {
    private static final SolverType Z3_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("Z3"))
            .findFirst().orElse(null);

    private static final Path VALID_LIST_PATH = Paths.get("/tmp/valid_list.txt");

    private static final Set<Path> VALID_SET = new HashSet<>();

    private static final Map<Path, Map<String, Map<Goal, StatEntry>>> STATS = new HashMap<>();

    private static final PrintStream STDOUT = System.out;
    private static final PrintStream STDERR = System.err;

    private static final long timeoutSeconds = 30;

    private static Path outDir;

    private static boolean skipProvable = false;

    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    private static final Collection<Path> flaggedTranslations = new HashSet<>();

    private static class StatEntry {
        final Path p;
        ProofState keyState = ProofState.UNKNOWN;
        long keyTime;
        int keyNodes;
        long z3TranslationLines;
        long translationAndZ3Time;
        long z3ProofLines;
        ProofState z3State;
        String z3ErrorMessage;
        long isabelleBuildTime;
        long isabelleParseTime;
        long isabelleSledgehammerTime;
        long isabelleTotalTime;
        long isabelleTranslationLines;
        String isabelleProofTactic;
        ProofState isabelleState = ProofState.UNKNOWN;

        StatEntry(Path p) {
            this.p = p;
        }
    }

    private enum ProofState {
        UNKNOWN,
        ERROR,
        OPEN,
        CLOSED
    }

    public static void main(String[] args) {
        outDir = Paths.get("/tmp/benchmark"
                + System.currentTimeMillis());
        try {
            Files.createDirectories(outDir);
        } catch (IOException e) {
            e.printStackTrace();
        }

        if (args.length > 0 && args[0].equals("--create-provable-list")) {
            if (args.length > 1) {
                skipProvable = Boolean.parseBoolean(args[1]);
            }
            updateZ3ProvableList();
        } else {
            run();
        }
    }

    private static void run() {
        List<String> pathStrings;
        try {
            pathStrings = Files.readAllLines(VALID_LIST_PATH);
        } catch (IOException e) {
            e.printStackTrace();
            return;
        }
        for (String s : pathStrings) {
            Path p = Paths.get(s);
            VALID_SET.add(p);
            processFile(p, true, true, true);
            saveStatisticsCSVFile(p);
            saveFlaggedTranslations();
        }
        saveStatisticsCSV();
    }

    private static void saveStatisticsCSVFile(Path input) {
        StringBuilder sb = new StringBuilder();

        sb.append("input_file");
        sb.append(",");
        sb.append("contractName");
        sb.append(",");
        sb.append("goalNodeName");
        sb.append(",");
        sb.append("KeY_state");
        sb.append(",");
        sb.append("Isabelle_state");
        sb.append(",");
        sb.append("Z3_State");
        sb.append(",");
        sb.append("KeY_time");
        sb.append(",");
        sb.append("KeY_proof_nodes");
        sb.append(",");
        sb.append("SMT_translation_lines");
        sb.append(",");
        sb.append("transl_+_Z3_time");
        sb.append(",");
        sb.append("Z3_proof_lines");
        sb.append(",");
        sb.append("Z3_error_msg");
        sb.append(",");
        sb.append("Isabelle_build_time");
        sb.append(",");
        sb.append("Isabelle_parse_time");
        sb.append(",");
        sb.append("Isabelle_sledgehammer_time");
        sb.append(",");
        sb.append("Isabelle_total_time");
        sb.append(",");
        sb.append("Isabelle_translation_lines");
        sb.append(",");
        sb.append("Isabelle_proof");
        sb.append(System.lineSeparator());

        Map<String, Map<Goal, StatEntry>> contractMap = STATS.get(input);

        contractMap.forEach((String c, Map<Goal, StatEntry> entryMap) -> entryMap.forEach((Goal goal, StatEntry entry) -> {
            sb.append(entry.p);
            sb.append(",");
            sb.append(c.replace(",", "_"));
            sb.append(",");
            sb.append(goal.node().getStepIndex());
            sb.append(",");
            sb.append(entry.keyState);
            sb.append(",");
            sb.append(entry.isabelleState);
            sb.append(",");
            sb.append(entry.z3State);
            sb.append(",");
            sb.append(entry.keyTime);
            sb.append(",");
            sb.append(entry.keyNodes);
            sb.append(",");
            sb.append(entry.z3TranslationLines);
            sb.append(",");
            sb.append(entry.translationAndZ3Time);
            sb.append(",");
            sb.append(entry.z3ProofLines);
            sb.append(",");
            sb.append(entry.z3ErrorMessage);
            sb.append(",");
            sb.append(entry.isabelleBuildTime);
            sb.append(",");
            sb.append(entry.isabelleParseTime);
            sb.append(",");
            sb.append(entry.isabelleSledgehammerTime);
            sb.append(",");
            sb.append(entry.isabelleTotalTime);
            sb.append(",");
            sb.append(entry.isabelleTranslationLines);
            sb.append(",");
            sb.append(entry.isabelleProofTactic);
            sb.append(System.lineSeparator());
        }));

        try {
            Files.write(Path.of(outDir + "/" + input.getParent().getFileName() + "_statistics.csv"), sb.toString().getBytes());
            LOGGER.info("Statistics CSV written to {}", outDir);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static void saveStatisticsCSV() {
        StringBuilder sb = new StringBuilder();

        sb.append("input_file");
        sb.append(",");
        sb.append("contractName");
        sb.append(",");
        sb.append("goalNodeName");
        sb.append(",");
        sb.append("KeY_state");
        sb.append(",");
        sb.append("KeY_time");
        sb.append(",");
        sb.append("KeY_proof_nodes");
        sb.append(",");
        sb.append("SMT_translation_lines");
        sb.append(",");
        sb.append("transl_+_Z3_time");
        sb.append(",");
        sb.append("Z3_proof_lines");
        sb.append(",");
        sb.append("Z3_State");
        sb.append(",");
        sb.append("Isabelle_build_time");
        sb.append(",");
        sb.append("Isabelle_parse_time");
        sb.append(",");
        sb.append("Isabelle_sledgehammer_time");
        sb.append(",");
        sb.append("Isabelle_total_time");
        sb.append(",");
        sb.append("Isabelle_translation_lines");
        sb.append(",");
        sb.append("Isabelle_proof");
        sb.append(",");
        sb.append("Isabelle_state");
        sb.append(System.lineSeparator());

        for (Map<String, Map<Goal, StatEntry>> contractMap : STATS.values()) {
            contractMap.forEach((String c, Map<Goal, StatEntry> entryMap) -> entryMap.forEach((Goal goal, StatEntry entry) -> {
                sb.append(entry.p);
                sb.append(",");
                sb.append(c.replace(",", "_"));
                sb.append(",");
                sb.append(goal.node().getStepIndex());
                sb.append(",");
                sb.append(entry.keyState);
                sb.append(",");
                sb.append(entry.isabelleState);
                sb.append(",");
                sb.append(entry.z3State);
                sb.append(",");
                sb.append(entry.keyTime);
                sb.append(",");
                sb.append(entry.keyNodes);
                sb.append(",");
                sb.append(entry.z3TranslationLines);
                sb.append(",");
                sb.append(entry.translationAndZ3Time);
                sb.append(",");
                sb.append(entry.z3ProofLines);
                sb.append(",");
                sb.append(entry.isabelleBuildTime);
                sb.append(",");
                sb.append(entry.isabelleParseTime);
                sb.append(",");
                sb.append(entry.isabelleSledgehammerTime);
                sb.append(",");
                sb.append(entry.isabelleTotalTime);
                sb.append(",");
                sb.append(entry.isabelleTranslationLines);
                sb.append(",");
                sb.append(entry.isabelleProofTactic);
                sb.append(System.lineSeparator());
            }));
        }

        try {
            Files.write(Path.of(outDir + "/statistics.csv"), sb.toString().getBytes());
            LOGGER.info("Statistics CSV written to {}", outDir);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static void loadValidSet() throws IOException {
        if (Files.exists(VALID_LIST_PATH)) {
            Files.lines(VALID_LIST_PATH).forEach(s -> VALID_SET.add(Paths.get(s)));
        }
    }

    private static void updateZ3ProvableList() {
        //Path exampleDir = FindResources.getExampleDirectory().toPath().toAbsolutePath().normalize();
        try {
            loadValidSet();
            List<Path> dirs = new ArrayList<>();
            //dirs.add(exampleDir);
            dirs.add(Paths.get(System.getProperty("user.home") + "/Desktop/examples"));

            Files.createDirectories(VALID_LIST_PATH.getParent());
            if (!Files.exists(VALID_LIST_PATH)) {
                Files.createFile(VALID_LIST_PATH);
            }

            for (Path dir : dirs) {
                Files.walkFileTree(dir, new FileVisitor<>() {

                    @Override
                    public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs)
                            throws IOException {
                        return FileVisitResult.CONTINUE;
                    }

                    @Override
                    public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
                        LOGGER.info("Visiting " + file.toString());
                        if (file.toString().endsWith(".key") && checkNonTrivialNoErrorQuickLoad(file)) {
                            appendValid(file.toAbsolutePath());
                        }
                        if (!skipProvable) {
                            processFile(file, false, true, false);
                        }
                        return FileVisitResult.CONTINUE;
                    }

                    @Override
                    public FileVisitResult visitFileFailed(Path file, IOException exc)
                            throws IOException {
                        return FileVisitResult.CONTINUE;
                    }

                    @Override
                    public FileVisitResult postVisitDirectory(Path dir, IOException exc)
                            throws IOException {
                        return FileVisitResult.CONTINUE;
                    }
                });
            }
        } catch (OutOfMemoryError e) {
            e.printStackTrace();
            // can not continue in a useful manner
            System.exit(-1);
        } catch (Throwable e) {
            // continue even if an exception is thrown
            e.printStackTrace();
        }
    }

    private static boolean checkNonTrivialNoErrorQuickLoad(Path file) {
        AtomicReference<ProofManagementApi> pm = new AtomicReference<>();
        AtomicBoolean success = new AtomicBoolean(true);
        Runnable task = () -> {
            try {
                pm.set(KeYApi.loadFromKeyFile(file.toFile()));
                success.set(true);
            } catch (ProblemLoaderException e) {
                LOGGER.error("Load error {}", e.getMessage());
            }
        };
        ExecutorService executorService = new ThreadPoolExecutor(1, 1, 0L, TimeUnit.MILLISECONDS, new LinkedBlockingDeque<>());

        TimeLimiter tl = SimpleTimeLimiter.create(executorService);
        try {
            tl.runWithTimeout(task, 30000, TimeUnit.MILLISECONDS);
        } catch (TimeoutException | InterruptedException e) {
            LOGGER.error("Load timeout {}", file);
            return false;
        }
        if (!success.get() || pm.get() == null) {
            LOGGER.error("Load failed {}", file);
            return false;
        }


        ProofApi papi = pm.get().getLoadedProof();

        if (papi == null || papi.getProof() == null || papi.getProof().closed() || papi.getFirstOpenGoal() == null) {
            for (Contract contract : pm.get().getProofContracts()) {
                if (!checkTrivialNoErrorQuickLoadContract(file, contract, pm.get(), tl)) {
                    return false;
                }
            }
            return true;
        }

        LOGGER.info("Loaded {}", file);

        Node n = papi.getFirstOpenGoal().getProofNode();
        Proof proof = n.proof();


        Runnable prep = () -> {
            SMTPreparationMacro smtMacro = new SMTPreparationMacro();
            if (smtMacro.canApplyTo(proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null)) {
                try {
                    smtMacro.applyTo(null, proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null, null);
                    LOGGER.info("Prep done {}", file);
                    success.set(true);
                } catch (Exception e) {
                    e.printStackTrace();
                    success.set(false);
                }
            } else {
                LOGGER.error("Prep failed {}", file);
                success.set(false);
            }
        };

        try {
            tl.runWithTimeout(prep, 60, TimeUnit.SECONDS);
        } catch (TimeoutException | InterruptedException e) {
            LOGGER.error("Prep timeout {}", file);
            executorService.shutdown();
            return false;
        }
        if (!success.get()) {
            LOGGER.error("Prep failed {}", file);
            executorService.shutdown();
            return false;
        }

        if (proof.openGoals().isEmpty()) {
            LOGGER.error("No open goals found after Preparation {}", file);
            executorService.shutdown();
            return false;
        }
        executorService.shutdown();
        return true;
    }

    private static boolean checkTrivialNoErrorQuickLoadContract(Path file, Contract contract, ProofManagementApi pm, TimeLimiter tl) {
        ProofApi papi;
        try {
            papi = pm.startProof(contract);
        } catch (ProofInputException e) {
            e.printStackTrace();
            LOGGER.error("Failed to load contract: " + contract.getDisplayName());
            return false;
        }

        Node n = papi.getFirstOpenGoal().getProofNode();
        Proof proof = n.proof();


        AtomicBoolean success = new AtomicBoolean(true);

        Runnable prep = () -> {
            SMTPreparationMacro smtMacro = new SMTPreparationMacro();
            if (smtMacro.canApplyTo(proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null)) {
                try {
                    smtMacro.applyTo(null, proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null, null);
                    LOGGER.info("Prep done {}", file);
                    success.set(true);
                } catch (Exception e) {
                    e.printStackTrace();
                    success.set(false);
                }
            } else {
                LOGGER.error("Prep failed {}", file);
                success.set(false);
            }
        };

        try {
            tl.runWithTimeout(prep, timeoutSeconds, TimeUnit.SECONDS);
        } catch (TimeoutException | InterruptedException e) {
            LOGGER.error("Prep timeout {}", file);
            return false;
        }
        if (!success.get()) {
            LOGGER.error("Prep failed {}", file);
            return false;
        }
        return true;
    }


    private static void processFile(Path input, boolean runKeY, boolean runZ3, boolean runIsabelle) {
        if (input.toString().endsWith(".key")) {
            ProofApi papi = null;
            try {
                LOGGER.info("Processing " + input);
                ProofManagementApi pm = KeYApi.loadFromKeyFile(input.toFile());
                papi = pm.getLoadedProof();

                if (papi.getProof() == null) {
                    for (Contract contract : pm.getProofContracts()) {
                        processContract(pm, contract, input, runKeY, runZ3, runIsabelle);
                    }
                    return;
                }

                Proof proof = papi.getFirstOpenGoal().getProofNode().proof();
                UserInterfaceControl uic = new DefaultUserInterfaceControl();

                SMTPreparationMacro smtMacro = new SMTPreparationMacro();
                FullPropositionalExpansionMacro expansionMacro = new FullPropositionalExpansionMacro();
                if (smtMacro.canApplyTo(proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null)) {
                    try {
                        smtMacro.applyTo(uic, proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null, null);
                        LOGGER.info("Prep done, {} goals remaining", papi.getProof().openGoals().size());
                        expansionMacro.applyTo(uic, papi.getProof(), papi.getProof().openGoals(), null, null);
                        LOGGER.info("Expansion done, {} goals remaining", papi.getProof().openGoals().size());
                    } catch (Exception e) {
                        e.printStackTrace();
                        return;
                    }
                }
                if (proof.openGoals().isEmpty()) {
                    LOGGER.info("No open goals found after Preparation");
                    return;
                }
                ImmutableList<Goal> goals = proof.openGoals();


                STATS.put(input, new HashMap<>());
                STATS.get(input).put("", new HashMap<>());

                if (runIsabelle) {
                    runIsabelleToFile(input, "", goals);
                }
                if (runZ3) {
                    runZ3ToFile(input, "", goals, false);
                }
                if (runKeY) {
                    runWithKeYAuto(input, "", goals);
                }
                papi.getEnv().dispose();
            } catch (ProblemLoaderException | IOException e) {
                e.printStackTrace();
            } finally {
                if (papi != null) {
                    papi.getEnv().dispose();
                }
            }
        }
    }

    private static void processContract(ProofManagementApi pm, Contract contract, Path input, boolean runKeY, boolean runZ3, boolean runIsabelle) throws IOException, ProblemLoaderException {
        ProofApi papi = null;
        try {
            papi = pm.startProof(contract);
        } catch (ProofInputException e) {
            e.printStackTrace();
            LOGGER.error("Problem starting proof {}", e.getMessage());
            return;
        }

        Proof proof = papi.getFirstOpenGoal().getProofNode().proof();
        UserInterfaceControl uic = new DefaultUserInterfaceControl();

        String contractName = proof.name().toString();
        LOGGER.info("Processing contract " + contractName + " of " + input);


        SMTPreparationMacro smtMacro = new SMTPreparationMacro();
        FullPropositionalExpansionMacro expansionMacro = new FullPropositionalExpansionMacro();
        if (smtMacro.canApplyTo(proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null)) {
            try {
                smtMacro.applyTo(uic, proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null, null);
                LOGGER.info("Prep done, {} goals remaining", papi.getProof().openGoals().size());
                expansionMacro.applyTo(uic, papi.getProof(), papi.getProof().openGoals(), null, null);
                LOGGER.info("Expansion done, {} goals remaining", papi.getProof().openGoals().size());
            } catch (Exception e) {
                e.printStackTrace();
                return;
            }
        }
        if (proof.openGoals().isEmpty()) {
            LOGGER.info("No open goals found after Preparation");
            return;
        }
        ImmutableList<Goal> goals = proof.openGoals();

        STATS.computeIfAbsent(input, k -> new HashMap<>());
        STATS.get(input).put(proof.name().toString(), new HashMap<>());

        if (runIsabelle) {
            runIsabelleToFile(input, proof.name().toString(), goals);
        }
        if (runZ3) {
            runZ3ToFile(input, proof.name().toString(), goals, false);
        }
        if (runKeY) {
            runWithKeYAuto(input, proof.name().toString(), goals);
        }
        papi.getEnv().dispose();
    }

    private static void runWithKeYAuto(Path input, String contractName, ImmutableList<Goal> goals) throws ProblemLoaderException, IOException {
        Proof proof = goals.stream().findFirst().get().proof();
        UserInterfaceControl uic = new DefaultUserInterfaceControl();

        // this should initialize with the default properties,
        // necessary to enable quantifier instantiation
        StrategyProperties properties = new StrategyProperties();
        Strategy strategy = new JavaCardDLStrategyFactory().create(proof, properties);
        proof.setActiveStrategy(strategy);
        proof.getSettings().getStrategySettings().setMaxSteps(Integer.MAX_VALUE);
        proof.getSettings().getStrategySettings().setTimeout(timeoutSeconds * 1000);

        for (Goal g : goals) {
            int nodes = -g.proof().getStatistics().nodes;
            long goalTime = g.node().getStepIndex();

            long manualTime = System.currentTimeMillis();
            uic.getProofControl().startFocussedAutoMode(null, g);
            uic.getProofControl().waitWhileAutoMode();
            manualTime = System.currentTimeMillis() - manualTime;

            Statistics statistics = g.proof().getStatistics();

            nodes += statistics.nodes;
            updateKeYNodes(input, contractName, g, nodes);

            long keyTime = statistics.autoModeTimeInMillis;
            LOGGER.info("   KeY statistics: " + keyTime);
            LOGGER.info("   Manual logging: " + manualTime);

            updateKeYState(input, contractName, g, !(g.proof().isOpenGoal(g.node())) ? ProofState.CLOSED : ProofState.OPEN);
            updateKeYTime(input, contractName, g, manualTime);
            Path proofPath = getOutPath(input, goalTime + "_key.proof");
            ProofSaver saver = new ProofSaver(g.proof(), proofPath.toFile());
            saver.save();
        }
    }

    private static void runZ3ToFile(Path input, String contractName, ImmutableList<Goal> goals, boolean tryReplay)
            throws ProblemLoaderException, IOException {

        Proof proof = goals.stream().findFirst().get().proof();

        ProofIndependentSMTSettings piSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
        piSettings.setTimeout(timeoutSeconds * 1000);
        SMTSettings settings = new DefaultSMTSettings(proof.getSettings().getSMTSettings(), piSettings,
                proof.getSettings().getNewSMTSettings(), proof);


        class TimedListener implements SolverLauncherListener {
            long translationAndZ3Time = 0;
            Goal goal;
            long goalNumber;

            public TimedListener(Goal g, long goalNumber) {
                goal = g;
                this.goalNumber = goalNumber;
            }

            @Override
            public void launcherStopped(SolverLauncher launcher,
                                        Collection<SMTSolver> finishedSolvers) {
                LOGGER.info("Z3 finished ({} solvers).", finishedSolvers.size());

                translationAndZ3Time = System.currentTimeMillis() - translationAndZ3Time;
                for (SMTSolver solver : finishedSolvers) {
                    SMTProblem solverProblem = solver.getProblem();
                    updateZ3Time(input, contractName, goal, translationAndZ3Time);
                }

                // we exactly have that single solver
                if (finishedSolvers.size() != 1) {
                    return;
                }
                SMTSolver z3 = finishedSolvers.iterator().next();

                String smtTranslation = z3.getTranslation();
                updateZ3TranslationLines(input, contractName, goal, countLines(smtTranslation));
                try {
                    Files.write(getOutPath(input, goalNumber + "_translation.smt"), smtTranslation.getBytes());
                } catch (IOException e) {
                    e.printStackTrace();
                }

                String z3Proof = z3.getRawSolverOutput();


                if (z3.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID) {
                    updateZ3State(input, contractName, goal, ProofState.CLOSED);
                    try {
                        Path outPath = getOutPath(input, goalNumber + "_proof.smt2");
                        updateZ3ProofLines(input, contractName, goal, countLines(z3Proof));
                        Files.write(outPath, z3Proof.getBytes());
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                    System.setOut(STDOUT);
                    System.setErr(STDERR);
                } else {
                    updateZ3State(input, contractName, goal, ProofState.OPEN);
                }
                launcher.removeListener(this);
            }

            @Override
            public void launcherStarted(Collection<SMTProblem> problems,
                                        Collection<SolverType> solverTypes,
                                        SolverLauncher launcher) {
                translationAndZ3Time = System.currentTimeMillis();
                LOGGER.info("Running Z3 ...");
            }
        }

        Collection<Callable<Object>> launcherRunnables = new LinkedBlockingQueue<>();

        Stream<SMTProblem> problems = goals.stream().map(SMTProblem::new);
        Services services = proof.getServices();


        problems.forEach((SMTProblem problem) -> launcherRunnables.add(() -> {
            SolverLauncher launcher = new SolverLauncher(settings);
            launcher.addListener(new TimedListener(problem.getGoal(), problem.getGoal().node().getStepIndex()));
            try {
                launcher.launch(problem, services, Z3_SOLVER);
            } catch (Exception e) {
                LOGGER.error("Exception during Z3... {}", e.getMessage());
                e.printStackTrace();
                updateZ3State(input, contractName, problem.getGoal(), ProofState.ERROR);
                updateZ3State(input, contractName, problem.getGoal(), e.getMessage().replace(System.lineSeparator(), " ").replace(",", " "));
            }
            return null;
        }));

        ExecutorService executorService = new ThreadPoolExecutor(3, 3, 0L, TimeUnit.MILLISECONDS, new LinkedBlockingDeque<>());
        try {
            executorService.invokeAll(launcherRunnables);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        executorService.shutdown();
    }

    private static void runIsabelleToFile(Path input, String contractName, ImmutableList<Goal> goals)
            throws ProblemLoaderException, IOException {

        Proof proof = goals.stream().findFirst().get().proof();

        SMTSettings settings = new DefaultSMTSettings(proof.getSettings().getSMTSettings(),
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(), proof.getSettings().getNewSMTSettings(), proof);


        class TimedListener implements IsabelleSolverListener {
            private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleSolverListener.class);
            long sledgehammerTime = 0L;
            long parsingTime = 0L;
            long buildingTime = 0L;
            Goal goal;
            long goalNumber;
            long totalTime;

            public TimedListener(Goal g, long goalNumber) {
                goal = g;
                this.goalNumber = goalNumber;
            }

            @Override
            public void parsingStarted(IsabelleProblem problem) {
                parsingTime = System.currentTimeMillis();
            }

            @Override
            public void parsingFinished(IsabelleProblem problem) {
                parsingTime = System.currentTimeMillis() - parsingTime;
                updateIsabelleParseTime(input, contractName, goal, parsingTime);
            }

            @Override
            public void parsingFailed(IsabelleProblem problem, Exception e) {
                updateIsabelleState(input, contractName, goal, ProofState.ERROR);
                updateIsabelleProof(input, contractName, goal, e.getMessage().replace(System.lineSeparator(), " ").replace(",", " "));
            }

            @Override
            public void buildingStarted(IsabelleProblem problem) {
                buildingTime = System.currentTimeMillis();
            }

            @Override
            public void buildingFinished(IsabelleProblem problem) {
                buildingTime = System.currentTimeMillis() - buildingTime;
                updateIsabelleBuildTime(input, contractName, goal, buildingTime);
            }

            @Override
            public void buildingFailed(IsabelleProblem problem, Exception e) {
                updateIsabelleState(input, contractName, goal, ProofState.ERROR);
                updateIsabelleProof(input, contractName, goal, e.getMessage().replace(System.lineSeparator(), " ").replace(",", " "));
            }

            @Override
            public void processStarted(IsabelleProblem problem) {
                totalTime = System.currentTimeMillis();
                LOGGER.info("Started on goal {} of contract {} in file {}", goalNumber, contractName, input);
            }

            @Override
            public void processStopped(IsabelleProblem problem) {
                totalTime = System.currentTimeMillis() - totalTime;
                updateIsabelleTime(input, contractName, goal, totalTime);

                String isabelleTranslation = problem.getSequentTranslation();
                updateIsabelleTranslationLines(input, contractName, goal, countLines(isabelleTranslation + problem.getPreamble()));
                try {
                    Files.write(getOutPath(input, goalNumber + "_translation.thy"), isabelleTranslation.getBytes());
                } catch (IOException e) {
                    e.printStackTrace();
                }


                if (problem.getResult().isSuccessful()) {
                    updateIsabelleState(input, contractName, goal, ProofState.CLOSED);
                    String isabelleProof = problem.getResult().getSuccessfulTactic();
                    updateIsabelleProof(input, contractName, goal, isabelleProof);
                }

                LOGGER.info("Result: {}", problem.getResult());
            }

            @Override
            public void processTimeout(IsabelleProblem problem) {
                updateIsabelleState(input, contractName, goal, ProofState.OPEN);
            }

            @Override
            public void sledgehammerStarted(IsabelleProblem problem) {
                sledgehammerTime = System.currentTimeMillis();
            }

            @Override
            public void sledgehammerFinished(IsabelleProblem problem) {
                sledgehammerTime = System.currentTimeMillis() - sledgehammerTime;
                updateIsabelleSledgehammerTime(input, contractName, goal, sledgehammerTime);
            }

            @Override
            public void sledgehammerFailed(IsabelleProblem problem, Exception e) {
                updateIsabelleState(input, contractName, goal, ProofState.ERROR);
                updateIsabelleProof(input, contractName, goal, e.getMessage().replace(System.lineSeparator(), " ").replace(",", " "));
            }

            @Override
            public void processInterrupted(IsabelleProblem problem, Exception e) {

            }
        }
        Services services = proof.getServices();
        IsabelleTranslator translator = new IsabelleTranslator(services);
        IsabelleLauncher launcher = new IsabelleLauncher(IsabelleTranslationSettings.getInstance());
        List<IsabelleProblem> problems = new ArrayList<>();

        goals.forEach((Goal goal) -> {
            IsabelleProblem problem;
            try {
                problem = translator.translateProblem(goal);
            } catch (IllegalFormulaException e) {
                flaggedTranslations.add(input);
                LOGGER.error("Translation failed: {}", e.getMessage());
                return;
            }
            problem.addListener(new TimedListener(goal, goal.node().getStepIndex()));

            problems.add(problem);
        });
        launcher.try0ThenSledgehammerAll(problems, timeoutSeconds);
    }

    private static void saveFlaggedTranslations() {
        StringBuilder sb = new StringBuilder();
        flaggedTranslations.forEach(sb::append);

        try {
            Files.write(Path.of(outDir + "flagged.txt"), sb.toString().getBytes());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static void updateIsabelleProof(Path input, String contractName, Goal goal, String isabelleProof) {
        StatEntry stats = STATS.get(input).get(contractName).get(goal);
        if (stats == null) {
            stats = new StatEntry(input);
        }
        stats.isabelleProofTactic = isabelleProof;
        STATS.get(input).get(contractName).put(goal, stats);
    }

    private static void updateIsabelleTime(Path input, String contractName, Goal goal, long totalTime) {
        StatEntry stats = STATS.get(input).get(contractName).get(goal);
        if (stats == null) {
            stats = new StatEntry(input);
        }
        stats.isabelleTotalTime = totalTime;
        STATS.get(input).get(contractName).put(goal, stats);
    }

    private static void updateIsabelleState(Path input, String contractName, Goal goal, ProofState state) {
        StatEntry stats = STATS.get(input).get(contractName).get(goal);
        if (stats == null) {
            stats = new StatEntry(input);
        }
        stats.isabelleState = state;
        STATS.get(input).get(contractName).put(goal, stats);
    }

    private static void updateIsabelleSledgehammerTime(Path input, String contractName, Goal goal, long sledgehammerTime) {
        StatEntry stats = STATS.get(input).get(contractName).get(goal);
        if (stats == null) {
            stats = new StatEntry(input);
        }
        stats.isabelleSledgehammerTime = sledgehammerTime;
        STATS.get(input).get(contractName).put(goal, stats);
    }

    private static void updateIsabelleBuildTime(Path input, String contractName, Goal goal, long buildTime) {
        StatEntry stats = STATS.get(input).get(contractName).get(goal);
        if (stats == null) {
            stats = new StatEntry(input);
        }
        stats.isabelleBuildTime = buildTime;
        STATS.get(input).get(contractName).put(goal, stats);
    }

    private static void updateIsabelleParseTime(Path input, String contractName, Goal goal, long parseTime) {
        StatEntry stats = STATS.get(input).get(contractName).get(goal);
        if (stats == null) {
            stats = new StatEntry(input);
        }
        stats.isabelleParseTime = parseTime;
        STATS.get(input).get(contractName).put(goal, stats);
    }

    private static void updateIsabelleTranslationLines(Path input, String contractName, Goal goal, long lineCount) {
        StatEntry stats = STATS.get(input).get(contractName).get(goal);
        if (stats == null) {
            stats = new StatEntry(input);
        }
        stats.isabelleTranslationLines = lineCount;
        STATS.get(input).get(contractName).put(goal, stats);
    }

    private static void appendValid(Path keyPath) {
        try {
            if (!VALID_SET.contains(keyPath)) {
                VALID_SET.add(keyPath);
                Files.write(VALID_LIST_PATH, Collections.singleton(keyPath.toString()), APPEND);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static long countLines(String input) {
        return input.chars().filter(ch -> ch == '\n').count();
    }

    private static Path getOutPath(Path input, String newExt) {
        String origFileName = input.getFileName().toString();
        String name;
        if (origFileName.contains(".")) {
            name = origFileName.substring(0, origFileName.lastIndexOf('.'));
        } else {
            name = origFileName;
        }
        String prefixedName = input.getName(input.getNameCount() - 3)
                + "_" + input.getName(input.getNameCount() - 2)
                + "_" + name;
        String newName = prefixedName + newExt;
        return outDir.resolve(newName);
    }

    private static void updateZ3Time(Path p, String c, Goal g, long z3Time) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.translationAndZ3Time = z3Time;
        STATS.get(p).get(c).put(g, stats);
    }


    private static void updateZ3State(Path p, String c, Goal g, ProofState state) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.z3State = state;
        STATS.get(p).get(c).put(g, stats);
    }

    private static void updateZ3State(Path p, String c, Goal g, String msg) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.z3ErrorMessage = msg;
        STATS.get(p).get(c).put(g, stats);
    }

    private static void updateZ3TranslationLines(Path p, String c, Goal g, long z3TranslationLines) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.z3TranslationLines = z3TranslationLines;
        STATS.get(p).get(c).put(g, stats);
    }

    private static void updateZ3ProofLines(Path p, String c, Goal g, long z3ProofLines) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.z3ProofLines = z3ProofLines;
        STATS.get(p).get(c).put(g, stats);
    }

    private static void updateKeYNodes(Path p, String c, Goal g, int keyNodes) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.keyNodes = keyNodes;
        STATS.get(p).get(c).put(g, stats);
    }


    private static void updateKeYTime(Path p, String c, Goal g, long keyTime) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.keyTime = keyTime;
        STATS.get(p).get(c).put(g, stats);
    }

    private static void updateKeYState(Path p, String c, Goal g, ProofState keyState) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.keyState = keyState;
        STATS.get(p).get(c).put(g, stats);
    }
}
