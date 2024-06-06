package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.function.Supplier;

public class DecorateLegacy<T> implements IPromptStrategy<T>, LegacyVisitor<T> {
    protected IPromptStrategy<T> fallback;

    public DecorateLegacy(IPromptStrategy<T> fallback) {
        this.fallback = fallback;
    }

    //region PromptReasons

    public Iterable<Prompt> reason(UnknownReason reason, T o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(WrongJML reason, T o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(InvalidJava reason, T o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(NoJMLInRegion reason, T o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(NoJMlInSearchLocations reason, T o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(FirstPrompt reason, T o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    //endregion

    @Override
    public Iterable<Prompt> apply(PromptReason legacyReasons, T o, Supplier<PromptBuilder> newBuilder) {
        if (legacyReasons instanceof LegacyReasons) {
            return apply((LegacyReasons) legacyReasons, o, newBuilder);
        } else {
            return fallback.apply(legacyReasons, o, newBuilder);
        }
    }
}
