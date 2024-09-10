package org.key_project.llmsynth.benchmarks;

import org.key_project.llmsynth.ISearchNode;
import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.benchmarks.legacy.StrategyProvider;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyLoopInvariant;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyFunction;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifySubcontract;
import org.key_project.llmsynth.oracles.OracleGpt3_5_Turbo;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.*;
import java.util.function.*;

/**
 * The BenchmarkRunner is in charge of obtaining strategies according to a benchmark, exploring the implicit search tree and filling a Benchmark with its results.
 * @param <TFunc> User data for TaskSpecifyFunction
 * @param <TSub> User data for TaskSpecifySubcontract
 * @param <TLoop> User data for TaskSpecifyLoopInvariant
 */
public class BenchmarkRunner<TFunc, TSub, TLoop> {
    StrategyProvider<TaskSpecifyFunction, TFunc> funcStrategyProvider;
    StrategyProvider<TaskSpecifySubcontract, TSub> subStrategyProvider;
    StrategyProvider<TaskSpecifyLoopInvariant, TLoop> loopStrategyProvider;
    Function<LLMChoice, Consumer<ISearchNode> > selectOracle;
    BiFunction<LLMChoice, ControlParameters, Predicate<VerificationResult> > selectResultAcceptor;

    /**
     *
     * @param funcStrategyProvider A strategy provider for instances of TaskSpecifyFunction
     * @param subStrategyProvider A strategy provider for instances of TaskSpecifySubcontract
     * @param loopStrategyProvider A strategy provider for instances of TaskSpecifyLoopInvariant
     * @param selectOracle A factory method for creating an oracle. The oracle is expected to keep history of their send messages.
     * @param selectResultAcceptor A function that has a final say on whether a verified result should be actually accepted. Will be run on all verified results.
     */
    public BenchmarkRunner(
            StrategyProvider<TaskSpecifyFunction, TFunc> funcStrategyProvider,
            StrategyProvider<TaskSpecifySubcontract, TSub> subStrategyProvider,
            StrategyProvider<TaskSpecifyLoopInvariant, TLoop> loopStrategyProvider,
            Function<LLMChoice, Consumer<ISearchNode>> selectOracle,
            BiFunction<LLMChoice, ControlParameters, Predicate<VerificationResult>> selectResultAcceptor
    ) {
        this.funcStrategyProvider = funcStrategyProvider;
        this.subStrategyProvider = subStrategyProvider;
        this.loopStrategyProvider = loopStrategyProvider;
        this.selectOracle = selectOracle;
        this.selectResultAcceptor = selectResultAcceptor;
    }

    /**
     * If the given benchmark is not completed, the BenchmarkRunner will try to solve it and store appropriate data denominating it.
     * @param benchmark The benchmark to be completed
     */
    public void run(Benchmark benchmark) {
        if (benchmark.isFinished()) return;
        // this method is essentially only here to select the correct strategies and types
        // todo: this can be made fully independent of Type by yet another indirection, which may be added later
        // todo: it should be typesafe after making it independent

        BenchmarkParameters param = benchmark.params;
        ControlParameters ctl = param.controlParameters;

        Consumer<ISearchNode> llm_oracle = selectOracle.apply(param.oracle);
        Predicate<VerificationResult> acceptResult = selectResultAcceptor.apply(param.oracle, param.controlParameters);

        switch (param.task.tag) {
            // todo: refactor into parameterized subfuncitoncall
            case SPECIFY_FUNCTION: {
                var task = (TaskSpecifyFunction) param.task;
                ISearchStrategy<TFunc> strategy = funcStrategyProvider.selectStrategy(param.oracle, task);
                TFunc data = funcStrategyProvider.createUserData();
                Function<Prompt, VerificationResult> defaultVerificator = funcStrategyProvider.createDefaultVerificator(param.oracle, task);

                run(benchmark, ctl, param.task, llm_oracle, strategy, acceptResult, defaultVerificator, data);
                break;
            }
            case SPECIFY_SUBCONTRACT: {
                var task = (TaskSpecifySubcontract) param.task;
                ISearchStrategy<TSub> strategy = subStrategyProvider.selectStrategy(param.oracle, task);
                TSub data = subStrategyProvider.createUserData();
                Function<Prompt, VerificationResult> defaultVerificator = subStrategyProvider.createDefaultVerificator(param.oracle, task);

                run(benchmark, ctl, param.task, llm_oracle, strategy, acceptResult, defaultVerificator, data);
                break;
            }
            case SPECIFY_LOOP_INVARIANT: {
                var task = (TaskSpecifyLoopInvariant) param.task;
                ISearchStrategy<TLoop> strategy = loopStrategyProvider.selectStrategy(param.oracle, task);
                TLoop data = loopStrategyProvider.createUserData();
                Function<Prompt, VerificationResult> defaultVerificator = loopStrategyProvider.createDefaultVerificator(param.oracle, task);

                run(benchmark, ctl, param.task, llm_oracle, strategy, acceptResult, defaultVerificator, data);
                break;
            }
        }
    }

    private static <TUserData> void run(
            Benchmark benchmark,
            ControlParameters ctl,
            LLMTask task, // todo: this should be the concrete instance type (otherwise the visitor-hack is required)
            // todo: actually, the strategy selector can store it ...
            Consumer<ISearchNode> llm_oracle,
            ISearchStrategy<TUserData> strategy,
            Predicate<VerificationResult> acceptResult,
            Function<Prompt, VerificationResult> defaultVerificator,
            TUserData data
    ) {
        PriorityQueue<SearchNode<TUserData>> pq = new PriorityQueue<>((l, r) -> r.getDepth() - l.getDepth());
        List<SearchNode<TUserData>> roots = new ArrayList<>();

        // insert the restarts into the queue
        for (int i = 0; i < ctl.maxRestarts; i++) {
            // TODO: special prompt type that marks the prompt invisible / somehow dont print the first prompt?
            // todo: the prompt here could be used as a system message before everything else.
            var start = new SearchNode<TUserData>(null, PromptStatus.REJECTED, new FirstPrompt(i));

            roots.add(start);
            pq.add(start);
        }

        // now do almost a DFS on the elements, building up a search tree for later documentation
        // Note, that the DFS behaviour is guaranteed by the ordering imposed on the priority queue (deeper elements get prioritized)
        // Exact search order is not set in stone
        // This implementation explores each child, but then descends the first child, repeating this behaviour.
        // So it's not exacly  a DFS.
        int global_steps = 0;
        while (!pq.isEmpty()) {
            SearchNode<TUserData> node_to_explore = pq.poll();

            Supplier<SearchNodeBuilder<TUserData>> builderFactory = () -> {
                var b = new SearchNodeBuilder<TUserData>(node_to_explore);
                // todo: should the verificator also obtain knowledge of the parent here?
                b.setVerificator(defaultVerificator);
                // todo: should previous prompts be stored here, for ease of use in the oracle?
                return b;
            };

            Iterable<SearchNode<TUserData>> new_unexplored_nodes = strategy.apply(node_to_explore, builderFactory);

            // todo: do not expand the tree, if it's already too wide
            for(SearchNode<TUserData> searchNode : new_unexplored_nodes) {
                System.out.println("STEP " + global_steps++);
                assert searchNode.parent == node_to_explore;

                // todo: another for loop could be here, if the same prompt should be asked multiple times to exploit indeterminism
                // Prompt answer = llm_oracle.apply(reason_to_explore, prompt);
                ask_oracle(llm_oracle, searchNode);

                // todo: FIXME results lose parent info when they are accepted?
                VerificationResult result = searchNode.verificator.apply(searchNode.prompt);
                assert result.getPrompt() == searchNode.prompt;
                searchNode.setResult(result);
                node_to_explore.reactions.add(searchNode);

                if (result.isAccepted()) {
                    // do not lift, as this result has no reason for rejection (getReason() == null)
                    if (acceptResult.test(result)) {
                        // todo: stuff we do when it's correct (mainly just setting the BenchmarkResult)
                        // todo: aka: add the result as the finishing node that proves success
                        System.out.println("[BENCHMARK_RUNNER] SUCCESSFUL RESULT");
                        break;
                    }
                } else  if (searchNode.getDepth() < ctl.maxSearchDepth) {
                    pq.add(searchNode);
                }
            }
        }
        // todo: write the results into a file or onto a stream (like std::out)
    }

    /**
     *
     * @param llm_oracle
//     * @param reason
//     * @param searchNode
     * @return
     */
    private static void ask_oracle(Consumer<ISearchNode> llm_oracle, ISearchNode node) {
        Prompt prompt = node.getPrompt();
        if (prompt.isAnswered()) return;
        llm_oracle.accept(node);
        assert prompt.isAnswered();
    }

    /**
     * Factory method for simple instantiation of a BenchmarkRunner
     * @param token An access token for OpenAI
     * @param funcStrategyProvider Provider for TaskSpecifyFunction
     * @param subStrategyProvider Provider for TaskSpecifySubcontract
     * @param loopStrategyProvider Provider for TaskSpecifyLoopInvariant
     * @return A BenchmarkRunner that uses OpenAI's Gpt3.5-turbo as oracle
     * @param <TFunc> User data for TaskSpecifyFunction
     * @param <TSub> User data for TaskSpecifySubcontract
     * @param <TLoop> User data for TaskSpecifyLoopInvariant
     */
    public static <TFunc, TSub, TLoop> BenchmarkRunner<TFunc, TSub, TLoop> create(
            String token,
            StrategyProvider<TaskSpecifyFunction, TFunc> funcStrategyProvider,
            StrategyProvider<TaskSpecifySubcontract, TSub> subStrategyProvider,
            StrategyProvider<TaskSpecifyLoopInvariant, TLoop> loopStrategyProvider
    ) {
        var oracle = new OracleGpt3_5_Turbo(token);
        return new BenchmarkRunner<>(funcStrategyProvider, subStrategyProvider, loopStrategyProvider,
                choice -> oracle::answerPromptOnNode,
                (llmChoice, controlParameters) -> (r -> true));
    }
}
