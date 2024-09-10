package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.prompts.SearchNodeBuilder;

import java.util.function.Supplier;

/**
 * There was no JML found at a place where it was expected
 */
public class    NoJMlInSearchLocations extends LegacyReasons {
    public NoJMlInSearchLocations() {
        super("no jml in search locations");
    }

    @Override
    public <T> Iterable<SearchNode<T>> dispatch(LegacyVisitor<T> visitor, T o, Supplier<SearchNodeBuilder<T>> newBuilder) {
        return visitor.reason(this, o, newBuilder);
    }
}
