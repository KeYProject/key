package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.prompts.SearchNodeBuilder;

import java.util.function.Supplier;

/**
 * The reason of failure coulnd't be described further
 */
public class UnknownReason extends LegacyReasons {
    private String message;

    public UnknownReason(String message) {
        super("unknown reason");
        this.message = message;
    }

    public String getException() {
        return message;
    }

    @Override
    public <T> Iterable<SearchNode<T>> dispatch(LegacyVisitor<T> visitor, T o, Supplier<SearchNodeBuilder<T>> newBuilder) {
        return visitor.reason(this, o, newBuilder);
    }
}
