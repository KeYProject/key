package org.key_project.llmsynth;

import org.key_project.llmsynth.benchmarks.Benchmark;
import org.key_project.llmsynth.benchmarks.BenchmarkRunner;
import org.key_project.llmsynth.benchmarks.LLMChoice;
import org.key_project.llmsynth.benchmarks.LLMTask;
import org.key_project.llmsynth.benchmarks.legacy.StrategyProvider;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyFunction;
import org.key_project.llmsynth.oracles.OpenAIEndpoint;
import org.key_project.llmsynth.oracles.OracleEndpoint;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.DirectPrompt;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;
import org.key_project.llmsynth.verificators.LegacyVerificator;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.function.Supplier;

class UserData {
    OracleEndpoint gpt; // = new OpenAIEndpoint("TOKEN-READ_FROM_DISK", OpenAIEndpoint.MODEL_3_5_TURBO);
    List<PromptMessage> truist = new ArrayList<>();
    List<PromptMessage> norris = new ArrayList<>();
}

class CustomStrategy implements IPromptStrategy<UserData> {
    TaskSpecifyFunction task;

    public CustomStrategy(TaskSpecifyFunction task) {
        this.task = task;
    }

    private Iterable<Prompt> firstPrompt(FirstPrompt fst, UserData ud, Supplier<PromptBuilder> nb) {
        var norris = ud.norris;
        var truist = ud.truist;

        var n1 = nb.get().asSystemPrompt().textln("You are Chuck Norris. As such you only answer in a manner doing justice to Norris.").build();
        var t1 = nb.get().asSystemPrompt().textln("You only answer with truisms.").build();
        var t2 = nb.get().asUserPrompt().textln("").build(); // The standard prompt is a user-prompt, this serves only for clarification

        norris.add(n1);
        truist.add(t1);
        truist.add(t2);

        var t2_a = ud.gpt.ask(truist); // answer.getMessageType() == PromptType.ASSISTANT ; if you want to feed this into another agent, a new prompt (with user-type) should be created as almost shown below.
        truist.add(t2_a); // if we want to retain the answer in the history of the 'truist'-agent, we need to add it explicitly
        var n2 = nb.get().asUserPrompt().textln("What do you have to say to this:").textln(t2_a.getContent()).build();
        var n2_a = ud.gpt.ask(norris, n2); // this overload adds the message and its answer to history, implicitly (see in default implementation in OracleEndpoint)

        // we want to go to round 2 now, but without anything else?
        AnsweredPrompt det = nb.get().skipVerification().answerWith(n2_a.getContent());
        // det is now an empty prompt with an associated answer, the answer is sent to the verificator (which we skipped here)
        // as the verification was skipped, the next time this Strategy is called, it is with an instance of  "DirectPrompt" as PromptReason.
        return List.of(det);
    }

    @Override
    public Iterable<Prompt> apply(PromptReason reason, UserData ud, Supplier<PromptBuilder> nb) {
        if (reason instanceof FirstPrompt) {
            return firstPrompt((FirstPrompt) reason, ud, nb);
        } else if (reason instanceof DirectPrompt) {
            // Now (for example's sake) we decide that this suffices. We want to take the answer as a definite solution (and not use key validation as we haven't actually tried to solve the benchmark)
            // As changing the Prompt after it is build is forbidden at the moment, we change the verificator before building as well:
            var q = nb.get().setVerificator(PromptResult::accept).textln("Are you sure?").build();
            // the history was stored in norris and not cleared, so this is fine.
            var a = ud.gpt.ask(ud.norris, q);
            return AnsweredPrompt.iterableFrom(q, a);
        } else {
            throw new RuntimeException();
        }
    }
}

class CustomProvider implements  StrategyProvider<TaskSpecifyFunction, UserData> {
    String token;
    Path tmpfile;

    public CustomProvider(String token, Path tmpfile) {
        this.token = token;
        this.tmpfile = tmpfile;
    }

    @Override
    public IPromptStrategy<UserData> selectStrategy(LLMChoice oracle, TaskSpecifyFunction task) {
        return new CustomStrategy(task);
    }

    @Override
    public UserData createUserData() {
        var ud = new UserData();
        ud.gpt = new OpenAIEndpoint(token, OpenAIEndpoint.MODEL_3_5_TURBO);
        return ud;
    }

    @Override
    public Function<PromptAnswer, PromptResult> createDefaultVerificator(LLMChoice oracle, TaskSpecifyFunction task) {
        return LegacyVerificator.fromTask(oracle, task, tmpfile);
    }
}

/**
 * An example of how to customize/provide your own PromptStrategy
 */
public class CustomPromptExample {
    public static void run(String token, Path tmpfile, Benchmark benchmark) {
        var myProvider = new CustomProvider(token, tmpfile);
        var bm = BenchmarkRunner.create(token, myProvider, null, null);
        bm.run(benchmark);
    }
}
