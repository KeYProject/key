package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptBuilder;

import java.util.function.Supplier;

/**
 * There was no JML found, as the region it should looked for also didn't exist.
 */
public class NoJMLInRegion extends LegacyReasons {
    public NoJMLInRegion() {
        super("no jml in region");
    }

    @Override
    public <T> Iterable<Prompt> dispatch(LegacyVisitor<T> visitor, T o, Supplier<PromptBuilder> newBuilder) {
        return visitor.reason(this, o, newBuilder);
    }
}
