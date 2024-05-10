package org.key_project.llmsynth;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.function.Supplier;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.llmsynth.benchmarks.*;
import org.key_project.llmsynth.benchmarks.legacy.DecorateLegacy;
import org.key_project.llmsynth.benchmarks.legacy.InvalidJava;
import org.key_project.llmsynth.benchmarks.legacy.LegacyReasons;
import org.key_project.llmsynth.benchmarks.legacy.LegacySpecifyTopLevel;
import org.key_project.llmsynth.old_unused.OldBenchmark;
import org.key_project.llmsynth.old_unused.Utility;
import org.key_project.llmsynth.old_unused.Gpt3Prompt;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.DirectPrompt;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;
import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * Example application which proves all proof obligations of the source folder 'example' using KeY.
 *
 * @author Martin Hentschel
 */
public class Main {
    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    public static void main(String[] args) {
        BenchmarkParameters bp = new BenchmarkParameters();
        bp.controlParameters = new ControlParameters().setMaxRestarts(10).setMaxSeachDepth(10).setKeyTimeoutSeconds(100);
        bp.oracle = LLMChoice.GPT_3_5_TURBO;
        bp.name = "test";
        bp.task = new TaskSpecifyFunction(null, null); // todo: this should be a tag, as the tasks require different parameters they should be classes themselved
        // todo: continuation ... how to dispatch by task-type without to much casting-vodoo....
//        bp.relatedFiles = List.of(); // todo: the file
        Benchmark benchmark = new Benchmark(bp);

        LegacySpecifyTopLevel lstl = new LegacySpecifyTopLevel() {
            @Override
            public Iterable<Prompt> reason(InvalidJava reason, String o, Supplier<PromptBuilder> newBuilder) {
                // custom strategy for specific reason
                // With broaden(strat_for_reason) & combine(this), prompts can be added to a reason
                // otherwise, the decorator pattern can achieve similar things, if implemente d.
                return PromptStrategy.NO_PROMPTS;
            }
        };

        IPromptStrategy<PromptReason, String> broadened = lstl.broaden(LegacyReasons.class);

        IPromptStrategy<PromptReason, String> shortCutExtension = (r, s, nb) -> {
            if (r.getDepth() == 0 && r instanceof FirstPrompt) {
                var pb = nb.get();
                pb.textln("Answer the following questions like goofy would.");
                pb.textln("Do you understand?");
                pb.setVerificator(a -> PromptResult.reject(a, new DirectPrompt()));
                return List.of(pb.build());
            } else if (r instanceof DirectPrompt) {
                // a hack, to achieve the behavior as if nothing happened.
                // as the extended strategy can't deal with DirectPrompts, but with the first prompt
                return broadened.apply(r.getParent(), s, nb);
            } else return PromptStrategy.NO_PROMPTS;
        };

        BenchmarkRunner<String, Object, Object> bmr = new BenchmarkRunner<>() {
            @Override
            public IPromptStrategy<PromptReason, ?> selectPromptStrategy(LLMChoice oracle, LLMTaskTag task) {
                return shortCutExtension.orElse(broadened);
            }
        };

        var decorated = new DecorateLegacy(lstl) {
            @Override
            public Iterable<Prompt> reason(FirstPrompt reason, String o, Supplier<PromptBuilder> newBuilder) {
                var pb = newBuilder.get();
                pb.textln("Answer the following questions like goofy would.");
                pb.textln("Do you understand?");
                pb.setVerificator(a -> PromptResult.reject(a, new DirectPrompt()));
                return List.of(pb.build());
            }

            @Override
            public Iterable<Prompt> broad_apply(PromptReason r, String o, Supplier<PromptBuilder> newBuilder) {
                if (r instanceof DirectPrompt) {
                    return super.broad_apply(r.getParent(), o, newBuilder);
                } else return super.broad_apply(r, o, newBuilder);
            }
        };

        System.out.println("Hallo welt");
//        bmr.run(benchmark);
        // todo: do stuff with the benchmark result
    }

    /**
     * The program entry point.
     *
     * @param args The start parameters.
     */
    public static void old_main(String[] args) {
        String pwd = System.getProperty("user.dir");
        System.out.println(pwd);
        String home = System.getProperty("user.home");
        Path location = Path.of(args.length == 1 ? (args[0]) : ("./example/DemoTwo.java"));
        Path tmpFile = Path.of(home + "/uni/prak-gpt/tmp/working.java");

        String bench_folder = "/home/pat/uni/prak-gpt/data/case/";

        try {
            String token = Files.readAllLines(Path.of(home +"/.key/openai-key.txt")).get(0);
            benchit(token, bench_folder, OldBenchmark.benchmarks, tmpFile);
            demo(token, location, tmpFile);
        } catch (Exception e) {
            System.out.println(e);
        }
    }

    private static void benchit(String token, String bench_folder, String[] benchmarks, Path tmpFile) {
        int maxTries = 5;
        int repeats = 15;
        List<OldBenchmark> bmres = new ArrayList<>();
        for(String benchClass : benchmarks) {
            try{
                var bm = OldBenchmark.onClass( bench_folder, benchClass, token, maxTries, tmpFile, repeats);
                if (bm != null) bmres.add(bm);
            } catch (Exception e) {
                System.err.println(e.toString());
            }
        }
        for (var bm : bmres) {
            System.out.println(bm.getRepr());
        }
    }

    private static void demo(String token, Path location, Path tmpFile) {

        try {
            List<String> classLines = Files.readAllLines(location);
            Gpt3Prompt.specifyFunction(token, classLines, "g", false, "f", false, 5, tmpFile);
        } catch (Exception e) {
            System.out.println(e);
        }
    }

    private static void old_discovery(File location) {
        KeYEnvironment<?> env = null;
        // Path to the source code folder/file or to a *.proof file
        try {
            // Ensure that Taclets are parsed
            env = Utility.createKeyEnvironment(location, null, null, null);
            ImmutableList<ProgramVariable> projectionVariables = ImmutableList.fromList(new LinkedList<>());
            List<Contract> contracts = Utility.getContracts(env);
            Utility.printMethodOfContract(contracts.get(0));
            List<UnclosedProof> unclosedProofs = Utility.tryClosingProofsAndListUnclosed(env, contracts, false, projectionVariables);
        } catch (ProblemLoaderException e) {
            LOGGER.info("Exception at '{}'", location, e);
        } finally {
            if (env != null) env.dispose();
        }
    }
}
