package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.benchmarks.LLMChoice;
import org.key_project.llmsynth.benchmarks.LLMTask;
import org.key_project.llmsynth.prompts.*;

import java.util.function.Function;

public interface StrategyProvider<TTask extends LLMTask, T> {

    IPromptStrategy<PromptReason, T> selectStrategy(LLMChoice oracle, TTask task);

    T createUserData();

    Function<PromptAnswer, PromptResult> createDefaultVerificator(LLMChoice oracle, TTask task);

    static <TTask extends LLMTask, T> StrategyProvider<TTask, T> getDefault() {
        return new StrategyProvider<>() {
            @Override
            public IPromptStrategy<PromptReason, T> selectStrategy(LLMChoice oracle, TTask task) {
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
