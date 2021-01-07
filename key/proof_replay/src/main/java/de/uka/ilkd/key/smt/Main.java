package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;

import java.io.*;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.*;

import static java.nio.file.StandardOpenOption.APPEND;

public class Main {
    private static final Path VALID_LIST_PATH = Paths.get("C:\\Users\\Banach\\Desktop\\MA\\experiments\\valid_list.txt");

    private static final Set<Path> VALID_SET = new HashSet<>();

    private static final Map<Path, StatEntry> STATS = new HashMap<>();

    private static final PrintStream STDOUT = System.out;
    private static final PrintStream STDERR = System.err;

    private static Path outDir;

    private static class StatEntry {
        Path p;
        long keyTime;
        int keyNodes;
        long z3TranslationLines;
        long translationAndZ3Time;
        long z3ProofLines;
        long replayTime;
        int replayNodes;
        ProofState replayState = ProofState.UNKOWN;
    }

    private enum ProofState {
        UNKOWN,
        ERROR,
        OPEN,
        CLOSED
    }

    public static void main(String[] args) {

        if (Files.exists(VALID_LIST_PATH)) {
            run();
        } else {
            runFirstTime();
        }
    }

    private static void run() {
        outDir = Paths.get("C:\\Users\\Banach\\Desktop\\MA\\experiments\\benchmark"
            + System.currentTimeMillis());

        List<String> pathStrings = null;
        try {
            Files.createDirectories(outDir);
            pathStrings = Files.readAllLines(VALID_LIST_PATH);
        } catch (IOException e) {
            e.printStackTrace();
            return;
        }
        for (String s : pathStrings) {
            Path p = Paths.get(s);
            VALID_SET.add(p);
            processFile(p);
        }
        printStatistics();
    }

    private static void printStatistics() {
        // print to console
        System.setOut(STDOUT);
        System.setErr(STDERR);

        System.out.print("filename");
        System.out.print("                 ");
        System.out.print("KeY time");
        System.out.print("                 ");
        System.out.print("KeY proof nodes");
        System.out.print("                 ");
        System.out.print("SMT translation lines");
        System.out.print("                 ");
        System.out.print("transl + Z3 time");
        System.out.print("                 ");
        System.out.print("Z3 proof lines");
        System.out.print("                 ");
        System.out.print("replay time");
        System.out.print("                 ");
        System.out.print("replayed proof nodes");
        System.out.print("                 ");
        System.out.print("replay state");
        System.out.println();

        for (StatEntry statEntry : STATS.values()) {
            System.out.print(statEntry.p.getFileName());
            System.out.print("                 ");
            System.out.print(statEntry.keyTime);
            System.out.print("                 ");
            System.out.print(statEntry.keyNodes);
            System.out.print("                 ");
            System.out.print(statEntry.z3TranslationLines);
            System.out.print("                 ");
            System.out.print(statEntry.translationAndZ3Time);
            System.out.print("                 ");
            System.out.print(statEntry.z3ProofLines);
            System.out.print("                 ");
            System.out.print(statEntry.replayTime);
            System.out.print("                 ");
            System.out.print(statEntry.replayNodes);
            System.out.print("                 ");
            System.out.print(statEntry.replayState);
            System.out.println();
        }
    }

    private static void runFirstTime() {
        //Path exampleDir = FindResources.getExampleDirectory().toPath().toAbsolutePath().normalize();
        List<Path> dirs = new LinkedList<>();
        dirs.add(Paths.get("C:\\Users\\Banach\\Desktop\\KeY\\key\\key\\key.ui\\examples\\newBook\\Using_KeY"));
        dirs.add(Paths.get("C:\\Users\\Banach\\Desktop\\KeY\\key\\key\\key.ui\\examples\\smt"));
        dirs.add(Paths.get("C:\\Users\\Banach\\Desktop\\KeY\\key\\key\\key.ui\\examples\\standard_key"));
        dirs.add(Paths.get("C:\\Users\\Banach\\Desktop\\KeY\\key\\key\\key.ui\\examples\\firstTouch"));

        try {
            Files.createDirectories(VALID_LIST_PATH.getParent());
            Files.createFile(VALID_LIST_PATH);
        } catch (IOException e) {
            e.printStackTrace();
            return;
        }

        try {
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
                        processFile(file);
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

    private static void processFile(Path input) {
        if (input.toString().endsWith(".key")) {
            try {
                System.out.println("Processing " + input.toString());
                Path outPath = outDir.resolve(input.getName(input.getNameCount() - 2) + "_" +
                            input.getFileName().toString() + "_output.smt2");
                runeWithKeYAuto(input);
                runZ3ToFile(input);
            } catch (ProblemLoaderException | IOException e) {
                e.printStackTrace();
            }
        }
    }

    private static void runeWithKeYAuto(Path input) throws ProblemLoaderException {
        ProofManagementApi pm = KeYApi.loadFromKeyFile(input.toFile());
        ProofApi papi = pm.getLoadedProof();
        Proof proof = papi.getProof();

        UserInterfaceControl uic = new DefaultUserInterfaceControl();
        uic.getProofControl().startAndWaitForAutoMode(proof);

        int nodes = proof.getStatistics().nodes;
        updateKeYNodes(input, nodes);

        long keyTime = proof.getStatistics().autoModeTimeInMillis;
        if (proof.closed()) {
            updateKeYTime(input, keyTime);
        } else {
            updateKeYTime(input, -keyTime);
        }
        papi.getEnv().dispose();
    }

    private static void runZ3ToFile(Path input)
        throws ProblemLoaderException, IOException {

        ProofManagementApi pm = KeYApi.loadFromKeyFile(input.toFile());
        ProofApi papi = pm.getLoadedProof();

        if (papi == null || papi.getProof() == null || papi.getProof().closed() || papi.getFirstOpenGoal() == null) {
            return;
        }

        // currently we do not support files with Java programs
        if (pm.getProofContracts() == null || !pm.getProofContracts().isEmpty()) {
            return;
        }

        Node n = papi.getFirstOpenGoal().getProofNode();
        Proof proof = n.proof();

        //SMTProblem problem = new SMTProblem(n.sequent(), proof.getServices());
        SMTProblem problem = new SMTProblem(proof.openGoals().head());

        SMTSettings settings = new SMTSettings(proof.getSettings().getSMTSettings(),
            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(), proof);
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
                updateZ3TtranslationLines(input, countLines(smtTranslation));
                try {
                    Files.write(replaceExtension(input, "_translation.smt2"), smtTranslation.getBytes());
                } catch (IOException e) {
                    e.printStackTrace();
                }

                String z3Proof = z3.getSolverOutput();

                if (z3.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID) {
                    try {
                        appendValid(input);

                        Path outPath = replaceExtension(input, "_proof.smt2");
                        updateZ3ProofLines(input, countLines(z3Proof));
                        Files.write(outPath, z3Proof.getBytes());

                        tryReplay(problem, input);
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
        launcher.launch(problem, proof.getServices(), SolverType.Z3_NEW_TL_SOLVER);
    }

    private static <T> void appendValid(Path keyPath) {
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

    private static Path replaceExtension(Path path, String newExt) {
        //Path dir = path.getParent();
        Path fileName = path.getFileName();
        String name = fileName.toString().substring(0, fileName.toString().lastIndexOf('.'));
        String newName = name + newExt;
        return outDir.resolve(newName);
    }

    private static void tryReplay(SMTProblem problem, Path inPath) {
        try {
            SMTReplayer replayer = new SMTReplayer(problem);

            // prepare logging stdout to file
            Path log = replaceExtension(inPath, ".log");
            Path proofPath = replaceExtension(inPath, ".proof");

            PrintStream printStream = new PrintStream(log.toFile());
            System.setOut(printStream);
            System.setErr(printStream);

            long time = System.currentTimeMillis();
            replayer.replay();
            Proof proof = replayer.getProof();
            long replayTime = System.currentTimeMillis() - time;
            updateReplayTime(inPath, replayTime);
            updateReplayNodes(inPath, proof.getStatistics().nodes);

            if (proof.closed()) {
                System.out.println("Proof is closed!");

                ProofSaver saver = new ProofSaver(proof, proofPath.toFile());
                saver.save();

                updateReplayState(inPath, ProofState.CLOSED);
            } else {
                System.out.println("Proof is still open (" + proof.openGoals().size() + " goals)!");
                updateReplayState(inPath, ProofState.OPEN);
            }
        } catch (Throwable e) {
            // error in replay -> log to file
            e.printStackTrace();
            updateReplayState(inPath, ProofState.ERROR);
        }
    }

    private static void updateReplayTime(Path p, long replayTime) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry();
        }
        stats.replayTime = replayTime;
        STATS.put(p, stats);
    }


    private static void updateReplayNodes(Path p, int replayNodes) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry();
        }
        stats.replayNodes = replayNodes;
        STATS.put(p, stats);
    }

    private static void updateReplayState(Path p, ProofState replayState) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry();
        }
        stats.replayState = replayState;
        STATS.put(p, stats);
    }

    private static void updateZ3Time(Path p, long z3Time) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry();
        }
        stats.translationAndZ3Time = z3Time;
        STATS.put(p, stats);
    }

    private static void updateZ3TtranslationLines(Path p, long z3TranslationLines) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry();
        }
        stats.z3TranslationLines = z3TranslationLines;
        STATS.put(p, stats);
    }

    private static void updateZ3ProofLines(Path p, long z3ProofLines) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry();
        }
        stats.z3ProofLines = z3ProofLines;
        STATS.put(p, stats);
    }

    private static void updateKeYNodes(Path p, int keyNodes) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry();
        }
        stats.keyNodes = keyNodes;
        STATS.put(p, stats);
    }


    private static void updateKeYTime(Path p, long keyTime) {
        StatEntry stats = STATS.get(p);
        if (stats == null) {
            stats = new StatEntry();
        }
        stats.keyTime = keyTime;
        STATS.put(p, stats);
    }
}
