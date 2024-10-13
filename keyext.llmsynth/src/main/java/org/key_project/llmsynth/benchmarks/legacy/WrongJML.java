package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.prompts.SearchNodeBuilder;

import java.util.function.Supplier;

/**
 * The JML code was incorrect or failed to verify
 */
public class WrongJML extends LegacyReasons {
    private String message;
    private String jml;

    public WrongJML(String jml, String message) {
        super("wrong jml");
        this.jml = jml;
        this.message = message;
    }

    public String getException() {
        return message;
    }

    public String getJml() {
        return jml;
    }

    @Override
    public <T> Iterable<SearchNode<T>> dispatch(LegacyVisitor<T> visitor, T o, Supplier<SearchNodeBuilder<T>> newBuilder) {
        return visitor.reason(this, o, newBuilder);
    }
}
