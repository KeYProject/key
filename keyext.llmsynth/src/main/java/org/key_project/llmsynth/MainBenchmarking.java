package org.key_project.llmsynth;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.function.BiConsumer;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.key_project.llmsynth.benchmarks.*;
import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.benchmarks.legacy.*;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyFunction;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyLoopInvariant;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifySubcontract;
import org.key_project.llmsynth.oracles.OracleGpt3_5_Turbo;

import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
/**
 * Example application which proves all proof obligations of the source folder 'example' using KeY.
 */
public class MainBenchmarking {
    private static final Logger LOGGER = LoggerFactory.getLogger(MainBenchmarking.class);

    //private static final int ATTEMPTS = 3;
    private static final int ATTEMPTS = 1;

    //         return new SearchNode(List.of(p -> p.println(s)), a -> VerificationResult.reject(a, new DirectPrompt()), typ, false);
    private static void serialize_example() {
        // TODO: give reasons and do proper rejections
        Prompt a1 = new Prompt(PromptType.USER, "some root-string", "some inconspicuous answer");
        SearchNode<Nothing> r1 = new SearchNode<>(a1, PromptStatus.REJECTED, new WrongJML("test", null));

        Prompt a2_l = new Prompt(PromptType.USER, "left leaf", "very left");
        SearchNode<Nothing> r2_l = new SearchNode<>(a2_l, PromptStatus.REJECTED, new NoJMLInRegion());

        Prompt a2_r = new Prompt(PromptType.USER,"right leaf", "very right");
        SearchNode<Nothing> r2_r = new SearchNode<>(a2_r, PromptStatus.ACCEPTED, null);

        Prompt a3 = new Prompt(PromptType.USER, "left final leaf", "some addition");
        SearchNode<Nothing> r3 = new SearchNode<>(a3, PromptStatus.REJECTED, new UnknownReason(null));

        SearchNode<Nothing> root = new SearchNode<>(new FirstPrompt(0));
        // todo: make sure that the parent is set?
        root.reactions.add(r1);
        r1.reactions.add(r2_l);
        r1.reactions.add(r2_r);
        r2_l.reactions.add(r3);

        ObjectMapper om = new ObjectMapper();
        try {
            String serialized = om.writeValueAsString(root);
            System.out.println(serialized);
        } catch (JsonProcessingException e) {
            System.err.println(e);
        }
        System.exit(0);
    }

    public static void main(String[] args) {
        File benchmark_dir = args.length > 0 ? new File(args[0]) : new File("");
        File benchmark_dir_contract = new File(benchmark_dir, "contracts");
        File benchmark_dir_subcontracts = new File(benchmark_dir, "subcontracts");
        File benchmark_dir_invariants = new File(benchmark_dir, "invariants");

        serialize_example();

        File benchmark_filter = new File(args[1]);
        // Read lines of benchmark_filter into a list
        List<String> benchmark_list = null;
        try {
            benchmark_list = Files.readAllLines(benchmark_filter.toPath()).stream().map(String::trim).toList();
        } catch (IOException e) {
            System.err.println("Failed to read benchmark filter file " + benchmark_filter.getAbsolutePath());
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
            System.out.println("Setup failed");
            e.printStackTrace();
            System.exit(1);
        }
        final String token = tokenDraft;
        var benchmarkConfig = new ControlParameters().setMaxRestarts(1).setMaxSeachDepth(8).setKeyTimeoutSeconds(100);

        System.out.printf("Saving temporary files in %s", tmpfile);
        LegacyInterfaceFactory lsp = new LegacyInterfaceFactory(Path.of(tmpfile));
        // Task: Create a contract for the given method; we do not care about the method's surroundings
        StrategyProvider<TaskSpecifyFunction, Nothing> legacySpecifyFunctionProvider = lsp.getTaskSpecifyFunctionProvider();
        // Task: Create a contract for the given method; the contract must allow the verification of the top-level method
        StrategyProvider<TaskSpecifySubcontract, Nothing> legacySpecifySubcontractProvider = lsp.getTaskSpecifySubcontractProvider();
        // Task: Create a invariant for the method's loop; the invariant must allow the verification of the method's contract
        StrategyProvider<TaskSpecifyLoopInvariant, Nothing> legacySpecifyLoopinvariantProvider = lsp.getTaskSpecifyLoopInvariantProvider();

        OracleGpt3_5_Turbo.print_Messages = true;

        System.out.println("[BENCHMARK_RUNNER] BENCHMARK CATEGORY: CONTRACT");
        iterateDirectory(benchmark_dir_contract, benchmark_list,ATTEMPTS,  (ClassInfo ci, String methodname) -> {
            MethodInfo mi = new MethodInfo(methodname);
            BenchmarkParameters bp = new BenchmarkParameters();
            bp.controlParameters = benchmarkConfig;
            bp.oracle = LLMChoice.GPT_3_5_TURBO;
            bp.name = null;
            bp.task = new TaskSpecifyFunction(ci,mi);
            Benchmark benchmark = new Benchmark(bp);
            var bmr = BenchmarkRunner.create(token, legacySpecifyFunctionProvider, legacySpecifySubcontractProvider, legacySpecifyLoopinvariantProvider);

            bmr.run(benchmark);
        });

        System.out.println("[BENCHMARK_RUNNER] BENCHMARK CATEGORY: SUBCONTRACT");
        iterateDirectory(benchmark_dir_subcontracts, benchmark_list,ATTEMPTS,  (ClassInfo ci, String metadata) -> {
            var metadataSplit = metadata.split("\n");
            MethodInfo mi = new MethodInfo(metadataSplit[1]);
            MethodInfo mi2 = new MethodInfo(metadataSplit[0]);
            BenchmarkParameters bp = new BenchmarkParameters();
            bp.controlParameters = benchmarkConfig;
            bp.oracle = LLMChoice.GPT_3_5_TURBO;
            bp.name = null;
            bp.task = new TaskSpecifySubcontract(ci,mi,mi2);
            Benchmark benchmark = new Benchmark(bp);
            var bmr = BenchmarkRunner.create(token, legacySpecifyFunctionProvider, legacySpecifySubcontractProvider, legacySpecifyLoopinvariantProvider);

            bmr.run(benchmark);
        });

        System.out.println("[BENCHMARK_RUNNER] BENCHMARK CATEGORY: INVARIANT");
        iterateDirectory(benchmark_dir_invariants, benchmark_list,ATTEMPTS,  (ClassInfo ci, String methodname) -> {
            MethodInfo mi = new MethodInfo(methodname);
            BenchmarkParameters bp = new BenchmarkParameters();
            bp.controlParameters = benchmarkConfig;
            bp.oracle = LLMChoice.GPT_3_5_TURBO;
            bp.name = null;
            bp.task = new TaskSpecifyLoopInvariant(ci,mi);
            Benchmark benchmark = new Benchmark(bp);
            var bmr = BenchmarkRunner.create(token, legacySpecifyFunctionProvider, legacySpecifySubcontractProvider, legacySpecifyLoopinvariantProvider);

            bmr.run(benchmark);
        });

    }

    public static void iterateDirectory(File benchmark_dir, List<String> benchmark_list, int attempts, BiConsumer<ClassInfo, String> consumer) {
        for (File directories : benchmark_dir.listFiles()) {
            if (directories.isDirectory()) {
                // Find Java File in directory
                File[] files = directories.listFiles((dir, name) -> name.endsWith(".java"));
                if (files.length == 0) {
                    LOGGER.warn("No Java file found in directory {}", directories.getAbsolutePath());
                    continue;
                }
                File javaFile = files[0];
                boolean runBenchmark = false;
                for (String benchmark : benchmark_list) {
                    if (javaFile.getAbsolutePath().endsWith(benchmark)) {
                        runBenchmark = true;
                        break;
                    }
                }
                if (!runBenchmark) {
                    System.out.println("[BENCHMARK_RUNNER] Skipping " + javaFile.getAbsolutePath() + " because it is not in the benchmark list");
                    continue;
                }
                System.out.println("[BENCHMARK_RUNNER] FILE: " + javaFile.getAbsolutePath());
                File metadataFile = new File(directories, "meta.txt");
                String metadata = null;
                try {
                    metadata = Files.readString(metadataFile.toPath()).trim();
                } catch (IOException e) {
                    LOGGER.error("Failed to read metadata file {}", metadataFile.getAbsolutePath());
                    continue;
                }
                // Create ClassInfo object
                ClassInfo ci;
                try {
                    ci = new ClassInfo(javaFile.getName(),javaFile.toPath());
                } catch (IOException e) {
                    LOGGER.error("Failed to read Java file {}", javaFile.getAbsolutePath());
                    continue;
                }
                for (int i = 0; i < attempts; i++) {
                    System.out.println("[BENCHMARK_RUNNER] ATTEMPT: " + i);
                    boolean success = true;
                    int restarts = 0;
                    do {
                        try {
                            consumer.accept(ci, metadata);
                            System.out.flush();
                            System.err.flush();
                        } catch (Exception e) {
                            System.err.println(e);
                            e.printStackTrace();
                            success = false;
                            restarts++;
                            System.out.println("[BENCHMARK_RUNNER] RESTARTING: " + restarts);
                            try {
                                Thread.sleep(5000);
                            } catch (InterruptedException ignored) {}
                        }
                    } while (!success && restarts < 3);
                }
            }
        }
    }

}
