package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
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

    private static final List<StatEntry> STATS = new ArrayList<>();

    private static final PrintStream STDOUT = System.out;
    private static final PrintStream STDERR = System.err;

    private static class StatEntry {
        final long replayTime;
        final Path p;
        final ProofState state;

        StatEntry(long replayTime, Path p, ProofState state) {
            this.replayTime = replayTime;
            this.p = p;
            this.state = state;
        }
    }

    private enum ProofState {
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
            processFile(p);
        }
        printStatistics();
    }

    private static void printStatistics() {
        // print to console
        System.setOut(STDOUT);
        System.setErr(STDERR);

        System.out.print("filename");
        System.out.print("            ");
        System.out.print("state");
        System.out.print("            ");
        System.out.print("replay time");
        System.out.println();

        for (StatEntry statEntry : STATS) {
            System.out.print(statEntry.p.getFileName());
            System.out.print("            ");
            System.out.print(statEntry.state);
            System.out.print("            ");
            System.out.print(statEntry.replayTime);
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

    private static void processFile(Path file) {
        if (file.toString().endsWith(".key")) {
            try {
                System.out.println("Processing " + file.toString());
                Path outPath = Paths
                    .get("C:\\Users\\Banach\\Desktop\\MA\\experiments\\benchmark\\",
                        file.getName(file.getNameCount() - 2) +
                            file.getFileName().toString() + "_output.smt2");
                runZ3ToFile(file.toFile(), outPath.toFile());
            } catch (ProblemLoaderException e) {
                e.printStackTrace();
            }
        }
    }

    private static void runZ3ToFile(File input, File outPath) throws ProblemLoaderException {

        ProofManagementApi pm = KeYApi.loadFromKeyFile(input);
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
            @Override
            public void launcherStopped(SolverLauncher launcher,
                                        Collection<SMTSolver> finishedSolvers) {
                System.out.println("Z3 finished (" + finishedSolvers.size() + " solvers).");
                // we exactly have that single solver
                if (finishedSolvers.size() != 1) {
                    return;
                }
                SMTSolver z3 = finishedSolvers.iterator().next();
                String output = z3.getSolverOutput();

                if (z3.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID) {
                    try {
                        appendValid(input.toPath());
                        Files.write(outPath.toPath(), output.getBytes());
                        tryReplay(problem, input.toPath(), outPath.toPath());
                    } catch (IOException e) {
                        e.printStackTrace();
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

    private static void tryReplay(SMTProblem problem, Path inPath, Path outPath) {
        try {
            SMTReplayer replayer = new SMTReplayer(problem);

            // prepare logging stdout to file
            Path dir = outPath.getParent();
            Path fileName = outPath.getFileName();
            String name = fileName.toString().substring(0, fileName.toString().lastIndexOf('.'));
            Path log = dir.resolve(name + ".log");
            Path proofPath = dir.resolve(name + ".proof");

            PrintStream printStream = new PrintStream(log.toFile());
            System.setOut(printStream);
            System.setErr(printStream);

            long time = System.currentTimeMillis();
            replayer.replay();
            Proof proof = replayer.getProof();
            long timeDiff = System.currentTimeMillis() - time;

            if (proof.closed()) {
                System.out.println("Proof is closed!");

                ProofSaver saver = new ProofSaver(proof, proofPath.toFile());
                saver.save();

                STATS.add(new StatEntry(timeDiff, inPath, ProofState.CLOSED));
            } else {
                System.out.println("Proof is still open (" + proof.openGoals().size() + " goals)!");
                STATS.add(new StatEntry(timeDiff, inPath, ProofState.OPEN));
            }

        } catch (Throwable e) {
            // error in replay -> log to file
            e.printStackTrace();
            STATS.add(new StatEntry(-1, inPath, ProofState.ERROR));
        }
    }
}
