package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptBuilder;
import org.key_project.llmsynth.prompts.PromptReason;

import java.util.function.Supplier;

/**
 * Reasons used in the old design
 */
public abstract class LegacyReasons extends PromptReason {
    public abstract <T> Iterable<Prompt> dispatch(LegacyVisitor<T> visitor, T o, Supplier<PromptBuilder> newBuilder);
}
