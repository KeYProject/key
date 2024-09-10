package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.prompts.SearchNodeBuilder;

import java.util.function.Supplier;

/**
 * The reason of failure coulnd't be described further
 */
public class UnknownReason extends LegacyReasons {
    private Exception exception;

    public UnknownReason(Exception failureException) {
        super("unknown reason");
        this.exception = failureException;
    }

    public Exception getException() {
        return exception;
    }

    @Override
    public <T> Iterable<SearchNode<T>> dispatch(LegacyVisitor<T> visitor, T o, Supplier<SearchNodeBuilder<T>> newBuilder) {
        return visitor.reason(this, o, newBuilder);
    }
}
