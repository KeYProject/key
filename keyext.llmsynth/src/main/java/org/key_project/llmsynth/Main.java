package org.key_project.llmsynth;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.function.Function;
import java.util.function.Supplier;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.llmsynth.benchmarks.*;
import org.key_project.llmsynth.benchmarks.legacy.*;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyFunction;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyLoopInvariant;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifySubcontract;
import org.key_project.llmsynth.old_unused.OldBenchmark;
import org.key_project.llmsynth.old_unused.Utility;
import org.key_project.llmsynth.old_unused.Gpt3Prompt;
import org.key_project.llmsynth.oracles.OracleGpt3_5_Turbo;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;
import org.key_project.llmsynth.verificators.LegacyVerificator;
import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

class JustChatting extends PromptReason {}

class ChatFirstExt extends DecorateLegacy {
    public ChatFirstExt(IPromptStrategy<LegacyReasons, Nothing> fallback) {
        super(fallback);
    }

    @Override
    public Iterable<Prompt> reason(FirstPrompt reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.setVerificator(a -> PromptResult.reject(a, new JustChatting()));
        b.textln("From now on, whenever you answer, make a goofey quote first.");
        return List.of(b.build());
    }

    // todo: nur prompt adaptieren
}

/**
 * Example application which proves all proof obligations of the source folder 'example' using KeY.
 *
 * @author Martin Hentschel
 */
public class Main {
    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    public static void main(String[] args) throws IOException {
        String token = Files.readString(Path.of("/home/pat/repos/key-key/token")).trim();
        // todo: Kommentieren (was muss man tun, um das u modifizieren)
        ClassInfo ci = new ClassInfo("Demo", Path.of("/home/pat/repos/key-key/Demo.java"));
        MethodInfo mi_f = new MethodInfo("f");
        MethodInfo mi_g = new MethodInfo("g");

        //
        BenchmarkParameters bp = new BenchmarkParameters();
        bp.controlParameters = new ControlParameters().setMaxRestarts(1).setMaxSeachDepth(10).setKeyTimeoutSeconds(100);
        bp.oracle = LLMChoice.GPT_3_5_TURBO;
        bp.name = "test";
        bp.task = new TaskSpecifyFunction(ci,mi_g);
        Benchmark benchmark = new Benchmark(bp);


        // Different tasks may require different strategies both depending on the task type and parameters, this will instantiate a strategy depending on these values
        // Key also requires an empty folder with a filename to be used, as it will load the whole folder during its own verification step
        // Therefore, a path to a filename in an otherwise empty folder should be given here as well
        LegacyStrategyProvider lsp = new LegacyStrategyProvider(Path.of("/home/pat/repos/key-key/tmp/tmpfile.java"));
        StrategyProvider<TaskSpecifyFunction, Nothing> legacySpecifyFunctionProvider = lsp.getTaskSpecifyFunctionProvider();
        StrategyProvider<TaskSpecifySubcontract, Nothing> legacySpecifySubcontractProvider = lsp.getTaskSpecifySubcontractProvider();
        StrategyProvider<TaskSpecifyLoopInvariant, Nothing> legacySpecifyLoopinvariantProvider = lsp.getTaskSpecifyLoopInvariantProvider();

        // Enable output of Prompts and answers so that they can be read
        OracleGpt3_5_Turbo.print_Messages = true;

        // The BenchmarkRunner will instantiate the proper strategies for each given benchmark and explore the solution-space according to the given parameters.
        var bmr = BenchmarkRunner.create(token, legacySpecifyFunctionProvider, legacySpecifySubcontractProvider, legacySpecifyLoopinvariantProvider);

        try {
            bmr.run(benchmark);
        } catch (Exception e) {
            System.err.println(e);
        }
        // todo: do stuff with the benchmark result
    }

}
