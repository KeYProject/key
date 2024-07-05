package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.benchmarks.LLMChoice;
import org.key_project.llmsynth.benchmarks.LLMTask;
import org.key_project.llmsynth.prompts.*;

import java.util.function.Function;

/**
 * A factory for PromptStrategies of a specific task
 * This aims to give each Benchmark a "clean-slate" to work with
 * @param <TTask> The type of the task
 * @param <TData> The user data type
 */
public interface StrategyProvider<TTask extends LLMTask, TData> {

    /**
     *
     * @param oracle The oracle to be used
     * @param task The task to be solved
     * @return A strategy that aims to solve the provided task
     */
    IPromptStrategy<TData> selectStrategy(LLMChoice oracle, TTask task);

    /**
     *
     * @return A new instance of userdata that may be weaved through all applications of the strategy
     */
    TData createUserData();

    /**
     *
     * @param oracle The oracle to be used
     * @param task The task to be solved
     * @return A verificator that can test, if a suggested solution solves the benchmark
     */
    Function<PromptAnswer, PromptResult> createDefaultVerificator(LLMChoice oracle, TTask task);

    /**
     *
     * @return Returns a StrategyProvider that does exactly nothing
     * @param <TTask> the task to be solved
     * @param <T> the user data type
     */
    static <TTask extends LLMTask, T> StrategyProvider<TTask, T> getDefault() {
        return new StrategyProvider<>() {
            @Override
            public IPromptStrategy<T> selectStrategy(LLMChoice oracle, TTask task) {
                return PromptStrategy.getDefault();
            }

            @Override
            public T createUserData() {
                return null;
            }

            @Override
            public Function<PromptAnswer, PromptResult> createDefaultVerificator(LLMChoice oracle, TTask task) {
                return null;
            }
        };
    }
}
