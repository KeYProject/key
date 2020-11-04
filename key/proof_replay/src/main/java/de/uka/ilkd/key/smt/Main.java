package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import org.key_project.util.helper.FindResources;

import java.io.File;
import java.io.IOException;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

public class Main {
    public static void main(String[] args) {

        //Path exampleDir = FindResources.getExampleDirectory().toPath().toAbsolutePath().normalize();
        List<Path> dirs = new LinkedList<>();
        dirs.add(Paths.get("C:\\Users\\Banach\\Desktop\\KeY\\key\\key\\key.ui\\examples\\newBook\\Using_KeY"));
        dirs.add(Paths.get("C:\\Users\\Banach\\Desktop\\KeY\\key\\key\\key.ui\\examples\\smt"));
        dirs.add(Paths.get("C:\\Users\\Banach\\Desktop\\KeY\\key\\key\\key.ui\\examples\\standard_key"));
        dirs.add(Paths.get("C:\\Users\\Banach\\Desktop\\KeY\\key\\key\\key.ui\\examples\\firstTouch"));

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
        } catch (Throwable e) {
            // continue even if an exception is thrown
            e.printStackTrace();
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

        SMTProblem problem = new SMTProblem(n.sequent(), proof.getServices());

        SMTSettings settings = new SMTSettings(proof.getSettings().getSMTSettings(),
            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(), proof);
        SolverLauncher launcher = new SolverLauncher(settings);

        launcher.addListener(new SolverLauncherListener() {
            @Override
            public void launcherStopped(SolverLauncher launcher,
                                        Collection<SMTSolver> finishedSolvers) {
                System.out.println("Z3 finished.");
                // we exactly have that single solver
                SMTSolver z3 = finishedSolvers.iterator().next();
                String output = z3.getSolverOutput();

                if (z3.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID) {
                    try {
                        Files.write(outPath.toPath(), output.getBytes());
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
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
}
