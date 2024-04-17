package evaluation;

import com.google.common.util.concurrent.SimpleTimeLimiter;
import com.google.common.util.concurrent.TimeLimiter;
import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.SMTPreparationMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
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
                    && it.getName().equals("Z3 (Legacy Translation)"))
            .findFirst().orElse(null);

    private static final Path VALID_LIST_PATH = Paths.get("/tmp/valid_list.txt");

    private static final Set<Path> VALID_SET = new HashSet<>();

    private static final Map<Path, Map<Contract, Map<Goal, StatEntry>>> STATS = new HashMap<>();

    private static final PrintStream STDOUT = System.out;
    private static final PrintStream STDERR = System.err;

    private static Path outDir;

    private static boolean skipProvable = false;

    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    private static class StatEntry {
        final Path p;
        ProofState keyState = ProofState.UNKNOWN;
        long keyTime;
        int keyNodes;
        long z3TranslationLines;
        long translationAndZ3Time;
        long z3ProofLines;
        SMTSolverResult.ThreeValuedTruth z3State;

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
        List<String> pathStrings = null;
        try {
            pathStrings = Files.readAllLines(VALID_LIST_PATH);
        } catch (IOException e) {
            e.printStackTrace();
            return;
        }
        for (String s : pathStrings) {
            Path p = Paths.get(s);
            VALID_SET.add(p);
            processFile(p, true, true, false);
        }
        saveStatisticsCSV();
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
        sb.append(System.lineSeparator());

        for (Map<Contract, Map<Goal, StatEntry>> contractMap : STATS.values()) {
            contractMap.forEach((Contract c, Map<Goal, StatEntry> entryMap) -> {
                entryMap.forEach((Goal goal, StatEntry entry) -> {
                    sb.append(entry.p);
                    sb.append(",");
                    sb.append(c.getDisplayName());
                    sb.append(",");
                    sb.append(goal.getTime());
                    sb.append(",");
                    sb.append(entry.keyState);
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
                    sb.append(entry.z3State);
                    sb.append(System.lineSeparator());
                });
            });
        }

        try {
            Files.write(Path.of(outDir + "/statistics.csv"), sb.toString().getBytes());
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
                Files.walkFileTree(dir, new FileVisitor<Path>() {

                    @Override
                    public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs)
                            throws IOException {
                        return FileVisitResult.CONTINUE;
                    }

                    @Override
                    public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
                        System.out.println("Visiting " + file.toString());
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
            tl.runWithTimeout(task, 60000, TimeUnit.MILLISECONDS);
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
            return false;
        }
        if (!success.get()) {
            LOGGER.error("Prep failed {}", file);
            return false;
        }

        if (proof.openGoals().isEmpty()) {
            LOGGER.error("No open goals found after Preparation {}", file);
            return false;
        }
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
            tl.runWithTimeout(prep, 60, TimeUnit.SECONDS);
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


    private static void processFile(Path input, boolean runKeY, boolean runZ3, boolean tryReplay) {
        if (input.toString().endsWith(".key")) {
            ProofApi papi = null;
            try {
                System.out.println("Processing " + input.toString());
                ProofManagementApi pm = KeYApi.loadFromKeyFile(input.toFile());
                papi = pm.getLoadedProof();

                if (papi.getProof() == null) {
                    for (Contract contract : pm.getProofContracts()) {
                        processContract(pm, contract, input, runKeY, runZ3);
                    }
                    return;
                }

                Proof proof = papi.getFirstOpenGoal().getProofNode().proof();
                UserInterfaceControl uic = new DefaultUserInterfaceControl();

                // this should initialize with the default properties,
                // necessary to enable quantifier instantiation
                StrategyProperties properties = new StrategyProperties();
                Strategy strategy = new JavaCardDLStrategyFactory().create(proof, properties);
                proof.setActiveStrategy(strategy);
                proof.getSettings().getStrategySettings().setMaxSteps(1000000);
                proof.getSettings().getStrategySettings().setTimeout(100000);

                SMTPreparationMacro smtMacro = new SMTPreparationMacro();
                if (smtMacro.canApplyTo(proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null)) {
                    try {
                        smtMacro.applyTo(uic, proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null, null);
                    } catch (Exception e) {
                        e.printStackTrace();
                        return;
                    }
                }
                if (proof.openGoals().isEmpty()) {
                    System.out.println("No open goals found after Preparation");
                    return;
                }
                ImmutableList<Goal> goals = proof.openGoals();


                STATS.put(input, new HashMap<>());
                STATS.get(input).put(null, new HashMap<>());


                if (runKeY) {
                    runWithKeYAuto(input, null, goals);
                }
                if (runZ3) {
                    runZ3ToFile(input, null, goals, false);
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

    private static void processContract(ProofManagementApi pm, Contract contract, Path input, boolean runKeY, boolean runZ3) throws IOException, ProblemLoaderException {
        System.out.println("Processing contract " + contract.getDisplayName() + " of " + input);

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

        // this should initialize with the default properties,
        // necessary to enable quantifier instantiation
        StrategyProperties properties = new StrategyProperties();
        Strategy strategy = new JavaCardDLStrategyFactory().create(proof, properties);
        proof.setActiveStrategy(strategy);
        proof.getSettings().getStrategySettings().setMaxSteps(1000000);
        proof.getSettings().getStrategySettings().setTimeout(100000);

        SMTPreparationMacro smtMacro = new SMTPreparationMacro();
        if (smtMacro.canApplyTo(proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null)) {
            try {
                smtMacro.applyTo(uic, proof, ImmutableList.of(proof.getOpenGoal(papi.getFirstOpenGoal().getProofNode())), null, null);
            } catch (Exception e) {
                e.printStackTrace();
                return;
            }
        }
        if (proof.openGoals().isEmpty()) {
            System.out.println("No open goals found after Preparation");
            return;
        }
        ImmutableList<Goal> goals = proof.openGoals();


        STATS.put(input, new HashMap<>());
        STATS.get(input).put(contract, new HashMap<>());


        if (runZ3) {
            runZ3ToFile(input, contract, goals, false);
        }
        if (runKeY) {
            runWithKeYAuto(input, contract, goals);
        }
        papi.getEnv().dispose();
    }

    private static void runWithKeYAuto(Path input, Contract contract, ImmutableList<Goal> goals) throws ProblemLoaderException, IOException {
        Proof proof = goals.stream().findFirst().get().proof();
        UserInterfaceControl uic = new DefaultUserInterfaceControl();

        // this should initialize with the default properties,
        // necessary to enable quantifier instantiation
        StrategyProperties properties = new StrategyProperties();
        Strategy strategy = new JavaCardDLStrategyFactory().create(proof, properties);
        proof.setActiveStrategy(strategy);
        proof.getSettings().getStrategySettings().setMaxSteps(1000000);
        proof.getSettings().getStrategySettings().setTimeout(1000);

        for (Goal g : goals) {
            long goalTime = g.getTime();

            long manualTime = System.currentTimeMillis();
            uic.getProofControl().startFocussedAutoMode(null, g);
            uic.getProofControl().waitWhileAutoMode();
            manualTime = System.currentTimeMillis() - manualTime;

            int nodes = g.proof().getStatistics().nodes;
            updateKeYNodes(input, contract, g, nodes);

            long keyTime = g.proof().getStatistics().autoModeTimeInMillis;
            System.out.println("   KeY statistics: " + keyTime);
            System.out.println("   Manual logging: " + manualTime);

            updateKeYState(input, contract, g, !(g.proof().isOpenGoal(g.node())) ? ProofState.CLOSED : ProofState.OPEN);
            updateKeYTime(input, contract, g, manualTime);
            Path proofPath = getOutPath(input, goalTime + "_key.proof");
            ProofSaver saver = new ProofSaver(g.proof(), proofPath.toFile());
            saver.save();
        }
    }

    private static void runZ3ToFile(Path input, Contract contract, ImmutableList<Goal> goals, boolean tryReplay)
            throws ProblemLoaderException, IOException {

        Proof proof = goals.stream().findFirst().get().proof();

        SMTSettings settings = new DefaultSMTSettings(proof.getSettings().getSMTSettings(),
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(), proof.getSettings().getNewSMTSettings(), proof);


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
                System.out.println("Z3 finished (" + finishedSolvers.size() + " solvers).");

                translationAndZ3Time = System.currentTimeMillis() - translationAndZ3Time;
                for (SMTSolver solver : finishedSolvers) {
                    SMTProblem solverProblem = solver.getProblem();
                    updateZ3Time(input, contract, goal, translationAndZ3Time);
                }

                // we exactly have that single solver
                if (finishedSolvers.size() != 1) {
                    return;
                }
                SMTSolver z3 = finishedSolvers.iterator().next();

                String smtTranslation = z3.getTranslation();
                updateZ3TranslationLines(input, contract, goal, countLines(smtTranslation));
                try {
                    Files.write(getOutPath(input, goalNumber + "_translation.smt"), smtTranslation.getBytes());
                } catch (IOException e) {
                    e.printStackTrace();
                }

                String z3Proof = z3.getRawSolverOutput();


                updateZ3State(input, contract, goal, z3.getFinalResult().isValid());
                if (z3.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID) {
                    try {
                        Path outPath = getOutPath(input, goalNumber + "_proof.smt2");
                        updateZ3ProofLines(input, contract, goal, countLines(z3Proof));
                        Files.write(outPath, z3Proof.getBytes());
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                    System.setOut(STDOUT);
                    System.setErr(STDERR);
                }
                launcher.removeListener(this);
            }

            @Override
            public void launcherStarted(Collection<SMTProblem> problems,
                                        Collection<SolverType> solverTypes,
                                        SolverLauncher launcher) {
                translationAndZ3Time = System.currentTimeMillis();
                System.out.println("Running Z3 ..." + translationAndZ3Time);
            }
        }

        Stream<SMTProblem> problems = goals.stream().map(SMTProblem::new);
        Services services = proof.getServices();

        problems.forEach((SMTProblem problem) -> {
            SolverLauncher launcher = new SolverLauncher(settings);
            launcher.addListener(new TimedListener(problem.getGoal(), problem.getGoal().getTime()));
            launcher.launch(problem, services, Z3_SOLVER);
        });
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

    private static void updateZ3Time(Path p, Contract c, Goal g, long z3Time) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.translationAndZ3Time = z3Time;
        STATS.get(p).get(c).put(g, stats);
    }


    private static void updateZ3State(Path p, Contract c, Goal g, SMTSolverResult.ThreeValuedTruth valid) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.z3State = valid;
        STATS.get(p).get(c).put(g, stats);
    }

    private static void updateZ3TranslationLines(Path p, Contract c, Goal g, long z3TranslationLines) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.z3TranslationLines = z3TranslationLines;
        STATS.get(p).get(c).put(g, stats);
    }

    private static void updateZ3ProofLines(Path p, Contract c, Goal g, long z3ProofLines) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.z3ProofLines = z3ProofLines;
        STATS.get(p).get(c).put(g, stats);
    }

    private static void updateKeYNodes(Path p, Contract c, Goal g, int keyNodes) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.keyNodes = keyNodes;
        STATS.get(p).get(c).put(g, stats);
    }


    private static void updateKeYTime(Path p, Contract c, Goal g, long keyTime) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.keyTime = keyTime;
        STATS.get(p).get(c).put(g, stats);
    }

    private static void updateKeYState(Path p, Contract c, Goal g, ProofState keyState) {
        StatEntry stats = STATS.get(p).get(c).get(g);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.keyState = keyState;
        STATS.get(p).get(c).put(g, stats);
    }
}
