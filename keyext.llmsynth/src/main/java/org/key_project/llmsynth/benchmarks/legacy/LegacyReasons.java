package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.prompts.SearchNodeBuilder;
import org.key_project.llmsynth.prompts.PromptReason;

import java.util.function.Supplier;

/**
 * Reasons used in the old design
 */
public abstract class LegacyReasons extends PromptReason {
    public LegacyReasons(String name) {
        super(name);
    }
    public abstract <T> Iterable<SearchNode<T>> dispatch(LegacyVisitor<T> visitor, T o, Supplier<SearchNodeBuilder<T>> newBuilder);
}
