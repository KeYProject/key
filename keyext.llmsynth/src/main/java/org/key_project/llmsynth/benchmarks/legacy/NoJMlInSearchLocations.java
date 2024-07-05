package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptBuilder;

import java.util.function.Supplier;

/**
 * There was no JML found at a place where it was expected
 */
public class    NoJMlInSearchLocations extends LegacyReasons {
    @Override
    public <T> Iterable<Prompt> dispatch(LegacyVisitor<T> visitor, T o, Supplier<PromptBuilder> newBuilder) {
        return visitor.reason(this, o, newBuilder);
    }
}
