package org.key_project.llmsynth.prompts.reasons;

import org.key_project.llmsynth.benchmarks.legacy.LegacyReasons;
import org.key_project.llmsynth.benchmarks.legacy.LegacyVisitor;
import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.prompts.SearchNodeBuilder;

import java.util.function.Supplier;

//todo: create FirstPrompt instances for each Tag

/**
 * The first prompt in history.
 * There were no previous prompts, and thus there can't be an answer.
 */
public class FirstPrompt extends LegacyReasons {
    private final int trialNumber;

    public FirstPrompt(int trialNumber) {
        super("first prompt");
        this.trialNumber = trialNumber;
    }

    public int getTrialNumber() {
        return trialNumber;
    }

    @Override
    public <T> Iterable<SearchNode<T>> dispatch(LegacyVisitor<T> visitor, T o, Supplier<SearchNodeBuilder<T>> newBuilder) {
        return visitor.reason(this, o, newBuilder);
    }
}
