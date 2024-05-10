package org.key_project.llmsynth.benchmarks;

import org.key_project.llmsynth.LLMTaskTag;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.IntStream;

public class BenchmarkRunner<TFunc, TSub, TLoop> {


    public void run(Benchmark benchmark) {
        if(benchmark.isFinished()) return;
        // this method is essentially only here to select the correct strategies and types
        // todo: this can be made fully independent of Type by yet another indirection, which may be added later
        // todo: it should be typesafe after making it independent

        BenchmarkParameters param = benchmark.params;
        ControlParameters ctl = param.controlParameters;

        BiFunction<PromptReason, Prompt, PromptAnswer> llm_oracle = selectOracle(param.oracle);
        Predicate<PromptResult> acceptResult = selectResultAcceptor(param.oracle, param.controlParameters);
        Function<PromptAnswer, PromptResult> defaultVerificator = selectDefaultVerificator(param.oracle, param.task.tag);

        switch(param.task.tag) {
            case SPECIFY_FUNCTION:
                IPromptStrategy<PromptReason, TFunc> strategy = (IPromptStrategy<PromptReason, TFunc>)selectPromptStrategy(param.oracle, param.task.tag);
                TFunc data = (TFunc)createUserData(param.oracle, param.controlParameters, param.task.tag);
                run(benchmark, ctl, param.task, llm_oracle, strategy, acceptResult, defaultVerificator, data);
                break;
            case SPECIFY_SUBCONTRACT:
            case SPECIFY_LOOP_INVARIANT:
                throw new UnsupportedOperationException("Not implemented!");
        }
    }

    private static <TUserData> void run(
            Benchmark benchmark,
            ControlParameters ctl,
            LLMTask task, // todo: this should be the concrete instance type (otherwise the visitor-hack is required)
            BiFunction<PromptReason, Prompt, PromptAnswer> llm_oracle,
            IPromptStrategy<PromptReason, TUserData> strategy,
            Predicate<PromptResult> acceptResult,
            Function<PromptAnswer, PromptResult> defaultVerificator,
            TUserData data
    ) {
        PriorityQueue<PromptReason> pq = new PriorityQueue<>((l, r) -> r.getDepth() - l.getDepth());
        Map<PromptReason, List<PromptResult>> tree = new HashMap<>();
        List<PromptReason> roots = new ArrayList<>();

        // insert the restarts into the queue
        for (int i = 0; i < ctl.maxRestarts; i++) {
            var start = FirstPrompt.create(task.tag, i);
            roots.add(start);
            pq.add(start);
        }

        // now do almost a DFS on the elements, building up a search tree for later documentation
        // Note, that the DFS behaviour is guaranteed by the ordering imposed on the priority queue (deeper elements get prioritized)
        // Exact search order is not set in stone
        // This implementation explores each child, but then descends the first child, repeating this behaviour.
        // So it's not exacly  a DFS.
        while (!pq.isEmpty()) {
            PromptReason reason_to_explore = pq.poll();

            Supplier<PromptBuilder> builderFactory = () -> {
                var b = new PromptBuilder();
                // todo: should the verificator also obtain knowledge of the parent here?
                b.setVerificator(defaultVerificator);
                // todo: should previous prompts be stored here, for ease of use in the oracle?
                return b;
            };

            Iterable<Prompt> prompts = strategy.apply(reason_to_explore, data, builderFactory);

            tree.put(reason_to_explore, new ArrayList<>());

            // todo: do not expand the tree, if it's already too wide
            for(Prompt prompt : prompts) {

                // todo: another for loop could be here, if the same prompt should be asked multiple times to exploit indeterminism
                PromptAnswer answer = llm_oracle.apply(reason_to_explore, prompt);
                assert answer.getPrompt() == prompt;

                // todo: FIXME results lose parent info when they are accepted?
                PromptResult result = prompt.verifyAnswer(answer);
                assert result.getAnswer() == answer;

                if (result.isAccepted()) {
                    // do not lift, as this result has no reason for rejection (getReason() == null)
                    if (acceptResult.test(result)) {
                        // we break, so the results won't be collected further down
                        tree.get(reason_to_explore).add(result);
                        // todo: stuff we do when it's correct (mainly just setting the BenchmarkResult)
                        // todo: aka: add the result as the finishing node that proves success
                        break;
                    }
                } else {
                    PromptReason child_rejection = result.getReason();
                    child_rejection.setParent(reason_to_explore);
                    child_rejection.setResult(result);
                    if (child_rejection.getDepth() < ctl.maxSearchDepth) {
                        pq.add(child_rejection);
                    }
                }
                tree.get(reason_to_explore).add(result);
            }
        }

        // todo: collect the results into the benchmark
    }

    public Object createUserData(LLMChoice oracle, ControlParameters controlParameters, LLMTaskTag task) {
        return null; // Expected to be overridden by the user
    }

    public Function<PromptAnswer, PromptResult> selectDefaultVerificator(LLMChoice oracle, LLMTaskTag task) {
        // todo: KeyVerification here
        throw new IllegalStateException("Not implemented");
    }

    public Predicate<PromptResult> selectResultAcceptor(LLMChoice oracle, ControlParameters controlParameters) {
        return x -> true;
    }

    public IPromptStrategy<PromptReason, ?> selectPromptStrategy(LLMChoice oracle, LLMTaskTag task) {
        // this is a no-op strategy, it will always yield an empty set
        return PromptStrategy.getDefault();
        // alternatively:
        // throw new IllegalStateException("Must be user provided");
    }

    public BiFunction<PromptReason, Prompt, PromptAnswer> selectOracle(LLMChoice oracle) {
        switch (oracle) {
            case GPT_3_5_TURBO:
                return null; // todo
            default:
                throw new IllegalStateException("Not implemented");
        }
    }




}
