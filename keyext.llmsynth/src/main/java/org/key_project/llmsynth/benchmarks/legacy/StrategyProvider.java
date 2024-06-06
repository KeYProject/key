package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.benchmarks.LLMChoice;
import org.key_project.llmsynth.benchmarks.LLMTask;
import org.key_project.llmsynth.prompts.*;

import java.util.function.Function;

public interface StrategyProvider<TTask extends LLMTask, TData> {

    IPromptStrategy<TData> selectStrategy(LLMChoice oracle, TTask task);

    TData createUserData();

    Function<PromptAnswer, PromptResult> createDefaultVerificator(LLMChoice oracle, TTask task);

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
