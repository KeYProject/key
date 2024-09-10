package org.key_project.llmsynth.prompts;

import org.key_project.llmsynth.SearchNode;

import java.util.function.Supplier;

/**
 * The main interface used to complete a benchmark.
 * Given A reason to prompt an oracle it shall provide possible prompts that may yield a solution to the problem described in the benchmark.
 * @param <TUserData> user data
 */
public interface ISearchStrategy<TUserData> {
    // TODO: think about having LLM specific PromptRequestBuilders (if PRB is right type then apply else fallback - with the 'last' fallback just throwing an error)
    Iterable<SearchNode<TUserData>> apply(SearchNode<TUserData> node, Supplier<SearchNodeBuilder<TUserData>> newBuilder);

    /**
     * Syntactic sugar
     * @param other the alternative
     * @return PromptStrategy.registerAlternativeWhenEmpty(self, other)
     */
    default ISearchStrategy<TUserData> orElse(ISearchStrategy<TUserData> other) {
        return SearchStrategy.registerAlternativeWhenEmpty(this, other);
    }

    /**
     * Syntactic sugar
     * @param other the strategy to be used after
     * @return PromptStrategy.combine(self, other)
     */
    default ISearchStrategy<TUserData> combine(ISearchStrategy<TUserData> other) {
        return SearchStrategy.combine(this, other);
    }

}
