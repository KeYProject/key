package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.function.Supplier;

/**
 * Override methods with the name 'reason' to change behaviour for processing according PromptReasons
 * @param <T>
 */
public class DecorateLegacy<T> implements ISearchStrategy<T>, LegacyVisitor<T> {
    private final ISearchStrategy<T> fallback;

    private SearchNode<T> node = null;
    Supplier<SearchNodeBuilder<T>> builder = null;

    public DecorateLegacy(ISearchStrategy<T> fallback) {
        this.fallback = fallback;
    }

    //region PromptReasons
    protected Iterable<SearchNode<T>> applyFallback() {
        return fallback.apply(node, builder);
    }
    
    public Iterable<SearchNode<T>> reason(UnknownReason reason, T o, Supplier<SearchNodeBuilder<T>>  newBuilder) {
        return applyFallback();
    }

    public Iterable<SearchNode<T>>  reason(WrongJML reason, T o, Supplier<SearchNodeBuilder<T>>  newBuilder) {
        return applyFallback();
    }

    public Iterable<SearchNode<T>>  reason(InvalidJava reason, T o, Supplier<SearchNodeBuilder<T>>  newBuilder) {
        return applyFallback();
    }

    public Iterable<SearchNode<T>>  reason(NoJMLInRegion reason, T o, Supplier<SearchNodeBuilder<T>>  newBuilder) {
        return applyFallback();
    }

    public Iterable<SearchNode<T>>  reason(NoJMlInSearchLocations reason, T o, Supplier<SearchNodeBuilder<T>>  newBuilder) {
        return applyFallback();
    }

    public Iterable<SearchNode<T>>  reason(FirstPrompt reason, T o, Supplier<SearchNodeBuilder<T>>  newBuilder) {
        return applyFallback();
    }

    //endregion

    @Override
    public Iterable<SearchNode<T>> apply(SearchNode<T> node, Supplier<SearchNodeBuilder<T>>  newBuilder) {
        try {
            this.node = node;
            this.builder = newBuilder;
            if (node.reason instanceof LegacyReasons r) {
                return  r.dispatch(this, node.userData, newBuilder);
            } else {
                return fallback.apply(node, newBuilder);
            }
        } finally {
            this.node = null;
            this.builder = null;
        }
    }
}
