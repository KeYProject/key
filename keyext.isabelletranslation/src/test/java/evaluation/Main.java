package evaluation;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;

import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.*;

import static java.nio.file.StandardOpenOption.APPEND;

public class Main {
    private static final SolverType Z3_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("Z3 (Legacy Translation)"))
            .findFirst().orElse(null);

    private static final Path VALID_LIST_PATH = Paths.get("/tmp/valid_list.txt");

    private static final Set<Path> VALID_SET = new HashSet<>();

    private static final Map<Path, StatEntry> STATS = new HashMap<>();

    private static final PrintStream STDOUT = System.out;
    private static final PrintStream STDERR = System.err;

    private static Path outDir;

    private static boolean skipProvable = false;

    private static class StatEntry {
        final Path p;
        ProofState keyState = ProofState.UNKNOWN;
        long keyTime;
        int keyNodes;
        long z3TranslationLines;
        long translationAndZ3Time;
        long z3ProofLines;

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
        sb.append(System.lineSeparator());

        for (StatEntry statEntry : STATS.values()) {
            sb.append(statEntry.p);
            sb.append(",");
            sb.append(statEntry.keyState);
            sb.append(",");
            sb.append(statEntry.keyTime);
            sb.append(",");
            sb.append(statEntry.keyNodes);
            sb.append(",");
            sb.append(statEntry.z3TranslationLines);
            sb.append(",");
            sb.append(statEntry.translationAndZ3Time);
            sb.append(",");
            sb.append(statEntry.z3ProofLines);
            sb.append(System.lineSeparator());
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
            dirs.add(Paths.get("D:/Uni/Bachelor-Arbeit/key/key.ui/examples/newBook/Using_KeY"));
            dirs.add(Paths.get("D:/Uni/Bachelor-Arbeit/key/key.ui/examples/smt"));
            dirs.add(Paths.get("D:/Uni/Bachelor-Arbeit/key/key.ui/examples/standard_key"));
            dirs.add(Paths.get("D:/Uni/Bachelor-Arbeit/key/key.ui/examples/firstTouch/"));

            Files.createDirectories(VALID_LIST_PATH.getParent());
            if (!Files.exists(VALID_LIST_PATH)) {
                Files.createFile(VALID_LIST_PATH);
            }

            StringBuilder sb = new StringBuilder();

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
                        if (file.toString().endsWith(".key")) {
                            sb.append(System.lineSeparator()).append(file.toAbsolutePath());
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
                Files.write(VALID_LIST_PATH, sb.toString().getBytes());
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

    private static void processFile(Path input, boolean runKeY, boolean runZ3, boolean tryReplay) {
        if (input.toString().endsWith(".key")) {
            try {
                System.out.println("Processing " + input.toString());
                if (runKeY) {
                    runeWithKeYAuto(input);
                }
                if (tryReplay) {
                    runZ3ToFile(input, true);
                } else if (runZ3) {
                    runZ3ToFile(input, false);
                }
            } catch (ProblemLoaderException | IOException e) {
                e.printStackTrace();
            }
        }
    }

    private static void runeWithKeYAuto(Path input) throws ProblemLoaderException, IOException {
        ProofManagementApi pm = KeYApi.loadFromKeyFile(input.toFile());
        ProofApi papi = pm.getLoadedProof();
        Proof proof = papi.getProof();
        UserInterfaceControl uic = new DefaultUserInterfaceControl();

        // this should initialize with the default properties,
        // necessary to enable quantifier instantiation
        StrategyProperties properties = new StrategyProperties();
        Strategy strategy = new JavaCardDLStrategyFactory().create(proof, properties);
        proof.setActiveStrategy(strategy);
        proof.getSettings().getStrategySettings().setMaxSteps(1000000);
        proof.getSettings().getStrategySettings().setTimeout(300000);

        long manualTime = System.currentTimeMillis();
        uic.getProofControl().startAndWaitForAutoMode(proof);
        manualTime = System.currentTimeMillis() - manualTime;

        int nodes = proof.getStatistics().nodes;
        updateKeYNodes(input, nodes);

        long keyTime = proof.getStatistics().autoModeTimeInMillis;
        System.out.println("   KeY statistics: " + keyTime);
        System.out.println("   Manual logging: " + manualTime);

        updateKeYState(input, proof.closed() ? ProofState.CLOSED : ProofState.OPEN);
        updateKeYTime(input, manualTime);
        Path proofPath = getOutPath(input, "_key.proof");
        ProofSaver saver = new ProofSaver(proof, proofPath.toFile());
        saver.save();

        papi.getEnv().dispose();
    }

    private static void runZ3ToFile(Path input, boolean tryReplay)
            throws ProblemLoaderException, IOException {

        ProofManagementApi pm = KeYApi.loadFromKeyFile(input.toFile());
        ProofApi papi = pm.getLoadedProof();

        if (papi == null || papi.getProof() == null || papi.getProof().closed() || papi.getFirstOpenGoal() == null) {
            return;
        }

        Node n = papi.getFirstOpenGoal().getProofNode();
        Proof proof = n.proof();

        //SMTProblem problem = new SMTProblem(n.sequent(), proof.getServices());
        SMTProblem problem = new SMTProblem(proof.openGoals().head());

        SMTSettings settings = new DefaultSMTSettings(proof.getSettings().getSMTSettings(),
                ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(), proof.getSettings().getNewSMTSettings(), proof);
        SolverLauncher launcher = new SolverLauncher(settings);

        launcher.addListener(new SolverLauncherListener() {
            long translationAndZ3Time = 0;

            @Override
            public void launcherStopped(SolverLauncher launcher,
                                        Collection<SMTSolver> finishedSolvers) {
                System.out.println("Z3 finished (" + finishedSolvers.size() + " solvers).");

                translationAndZ3Time = System.currentTimeMillis() - translationAndZ3Time;
                updateZ3Time(input, translationAndZ3Time);

                // we exactly have that single solver
                if (finishedSolvers.size() != 1) {
                    return;
                }
                SMTSolver z3 = finishedSolvers.iterator().next();

                String smtTranslation = z3.getTranslation();
                updateZ3TranslationLines(input, countLines(smtTranslation));
                try {
                    Files.write(getOutPath(input, "_translation.smt2"), smtTranslation.getBytes());
                } catch (IOException e) {
                    e.printStackTrace();
                }

                String z3Proof = z3.getRawSolverOutput();

                if (z3.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID) {
                    try {
                        appendValid(input);

                        Path outPath = getOutPath(input, "_proof.smt2");
                        updateZ3ProofLines(input, countLines(z3Proof));
                        Files.write(outPath, z3Proof.getBytes());
                    } catch (IOException e) {
                        e.printStackTrace();
                    } finally {
                        // try to avoid memory leaks
                        papi.getEnv().dispose();
                    }
                    System.setOut(STDOUT);
                    System.setErr(STDERR);
                }
            }

            @Override
            public void launcherStarted(Collection<SMTProblem> problems,
                                        Collection<SolverType> solverTypes,
                                        SolverLauncher launcher) {
                System.out.println("Running Z3 ...");
                translationAndZ3Time = System.currentTimeMillis();
            }
        });
        launcher.launch(problem, proof.getServices(), Z3_SOLVER);
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
        String name = origFileName.substring(0, origFileName.lastIndexOf('.'));
        String prefixedName = input.getName(input.getNameCount() - 3)
                + "_" + input.getName(input.getNameCount() - 2)
                + "_" + name;
        String newName = prefixedName + newExt;
        return outDir.resolve(newName);
    }

    private static void updateZ3Time(Path p, long z3Time) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.translationAndZ3Time = z3Time;
        STATS.put(p, stats);
    }

    private static void updateZ3TranslationLines(Path p, long z3TranslationLines) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.z3TranslationLines = z3TranslationLines;
        STATS.put(p, stats);
    }

    private static void updateZ3ProofLines(Path p, long z3ProofLines) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.z3ProofLines = z3ProofLines;
        STATS.put(p, stats);
    }

    private static void updateKeYNodes(Path p, int keyNodes) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.keyNodes = keyNodes;
        STATS.put(p, stats);
    }


    private static void updateKeYTime(Path p, long keyTime) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.keyTime = keyTime;
        STATS.put(p, stats);
    }

    private static void updateKeYState(Path p, ProofState keyState) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry(p);
        }
        stats.keyState = keyState;
        STATS.put(p, stats);
    }
}
