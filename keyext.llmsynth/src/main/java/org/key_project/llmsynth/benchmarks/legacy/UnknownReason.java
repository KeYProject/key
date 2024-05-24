package org.key_project.llmsynth.benchmarks.legacy;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptBuilder;

import java.util.function.Supplier;

public class UnknownReason extends LegacyReasons {
    private Exception exception;

    public UnknownReason(Exception failureException) {
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
