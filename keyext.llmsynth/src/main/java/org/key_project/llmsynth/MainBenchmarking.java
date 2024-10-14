package org.key_project.llmsynth;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.key_project.llmsynth.benchmarks.*;
import org.key_project.llmsynth.benchmarks.legacy.*;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyFunction;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyLoopInvariant;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifySubcontract;
import org.key_project.llmsynth.oracles.OracleGptDefault;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
/**
 * Example application which proves all proof obligations of the source folder 'example' using KeY.
 */
public class MainBenchmarking {
    private static final Logger LOGGER = LoggerFactory.getLogger(MainBenchmarking.class);

    //private static final int ATTEMPTS = 3;
    private static final int ATTEMPTS = 1;

    public static void main(String[] args) {
        if (args.length < 5) {
            System.err.println("Requires parameters: <strategy> <benchmark_directory> <restarts> <depth> <llm>");
            System.exit(1);
        }
        String strategy = args[0];
        File benchmark_dir = new File(args[1]);
        int restarts = Integer.parseInt(args[2]);
        int depth = Integer.parseInt(args[3]);
        String llm = args[4];

        LLMChoice llmChoice = LLMChoice.valueOf(llm);

        // Check if the benchmark directory exists
        if (!benchmark_dir.exists()) {
            System.err.println("Benchmark directory does not exist: " + benchmark_dir.getAbsolutePath());
            System.exit(1);
        }

        String tokenDraft="";
        File tmpdir;
        String tmpfile = "";
        try {
            tokenDraft = Files.readString(Path.of(System.getProperty("user.home") + "/.key/isola.txt")).trim();
            tmpdir = Files.createTempDirectory("keyLlmSynth").toFile();
            tmpfile = File.createTempFile("MyFile", ".java", tmpdir).getAbsolutePath();
        } catch (IOException e) {
            System.err.println("Setup failed");
            e.printStackTrace();
            System.exit(1);
        }

        final String token = tokenDraft;
        var benchmarkConfig = new ControlParameters().setMaxRestarts(restarts).setMaxSeachDepth(depth).setKeyTimeoutSeconds(100);

        System.err.printf("Saving temporary files in %s\n", tmpfile);
        LegacyInterfaceFactory lsp = new LegacyInterfaceFactory(Path.of(tmpfile));

        OracleGptDefault.print_Messages = false;

        // Find Java File in directory
        File[] files = benchmark_dir.listFiles((dir, name) -> name.endsWith(".java"));
        if (files.length == 0) {
            System.err.println("No Java file found in directory "+benchmark_dir.getAbsolutePath());
            System.exit(1);
        }
        File javaFile = files[0];

        // Find Metadata File in directory
        File metadataFile = new File(benchmark_dir, "meta.txt");
        String metadata = null;
        try {
            metadata = Files.readString(metadataFile.toPath()).trim();
        } catch (IOException e) {
            System.err.println("Failed to read metadata file "+metadataFile.getAbsolutePath());
            System.exit(1);
        }

        BenchmarkRunner bmr = null;
        String[] strategyParts = strategy.split("-");
        if (strategyParts.length != 2) {
            // Default strategy
            strategy = strategyParts[0];
            bmr = BenchmarkRunner.create(token, lsp.getTaskSpecifyFunctionProvider(), lsp.getTaskSpecifySubcontractProvider(), lsp.getTaskSpecifyLoopInvariantProvider());
        } else {
            strategy = strategyParts[0];
            switch (strategyParts[1]) {
                case "default":
                    bmr = BenchmarkRunner.create(token, lsp.getTaskSpecifyFunctionProvider(), lsp.getTaskSpecifySubcontractProvider(), lsp.getTaskSpecifyLoopInvariantProvider());
                    break;
                case "code":
                    bmr = BenchmarkRunner.create(token, lsp.getTaskSpecifyFunctionProviderCodeOnly(), lsp.getTaskSpecifySubcontractProviderCodeOnly(), lsp.getTaskSpecifyLoopInvariantProviderCodeOnly());
                    break;
                case "natural":
                    bmr = BenchmarkRunner.create(token, lsp.getTaskSpecifyFunctionProviderNatural(), lsp.getTaskSpecifySubcontractProviderNatural(), lsp.getTaskSpecifyLoopInvariantProviderNatural());
                    break;
                default:
                    System.err.println("Unknown strategy part: "+strategyParts[1]);
                    System.exit(1);
                    break;
            }
        }
        BenchmarkParameters bp = new BenchmarkParameters();
        ClassInfo ci = null;
        try {
            ci = new ClassInfo(javaFile.getName(),javaFile.toPath());
        } catch (IOException e) {
            System.err.println("Failed to read Java file "+javaFile.getAbsolutePath());
            System.exit(1);
        }
        MethodInfo mi;

        switch (strategy) {
            case "contracts":
                mi = new MethodInfo(metadata);
                bp.controlParameters = benchmarkConfig;
                bp.oracle = llmChoice;
                bp.name = null;
                bp.task = new TaskSpecifyFunction(ci,mi);
                break;
            case "subcontracts":
                var metadataSplit = metadata.split("\n");
                mi = new MethodInfo(metadataSplit[1]);
                MethodInfo mi2 = new MethodInfo(metadataSplit[0]);
                bp.controlParameters = benchmarkConfig;
                bp.oracle = llmChoice;
                bp.name = null;
                bp.task = new TaskSpecifySubcontract(ci,mi,mi2);
                break;
            case "invariants":
                mi = new MethodInfo(metadata);
                bp.controlParameters = benchmarkConfig;
                bp.oracle = llmChoice;
                bp.name = null;
                bp.task = new TaskSpecifyLoopInvariant(ci,mi);

                break;
            default:
                System.err.println("Unknown strategy: "+strategy);
                System.exit(1);
                break;
        }
        Benchmark benchmark = new Benchmark(bp);
        String benchmark_results = bmr.run(benchmark);
        System.out.println(benchmark_results);
        System.exit(0);
    }

}
