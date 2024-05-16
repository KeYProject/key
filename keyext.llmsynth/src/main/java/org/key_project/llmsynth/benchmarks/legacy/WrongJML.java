package org.key_project.llmsynth.benchmarks.legacy;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptBuilder;

import java.util.function.Supplier;

public class WrongJML extends LegacyReasons {
    private ProblemLoaderException exception;
    private String jml;

    public WrongJML(String jml, ProblemLoaderException failureException) {
        super();
        this.jml = jml;
        this.exception = failureException;
    }

    public ProblemLoaderException getException() {
        return exception;
    }

    public String getJml() {
        return jml;
    }

    @Override
    public <T> Iterable<Prompt> dispatch(LegacyVisitor<T> visitor, T o, Supplier<PromptBuilder> newBuilder) {
        return visitor.reason(this, o, newBuilder);
    }
}
