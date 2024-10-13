package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.prompts.SearchNodeBuilder;

import java.util.function.Supplier;

/**
 * The given code was not valid Java
 */
public class InvalidJava extends LegacyReasons {
    private String message;
    public InvalidJava(String message) {
        super("invalid java");
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
