package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptBuilder;

import java.util.function.Supplier;

public class InvalidJava extends LegacyReasons {
    private Exception exception;
    public InvalidJava(Exception failureException) {
        super();
        this.exception = failureException;
    }

    public Exception getException() {
        return exception;
    }

    @Override
    public <T> Iterable<Prompt> dispatch(LegacyVisitor<T> visitor, T o, Supplier<PromptBuilder> newBuilder) {
        return visitor.reason(this, o, newBuilder);
    }
}
