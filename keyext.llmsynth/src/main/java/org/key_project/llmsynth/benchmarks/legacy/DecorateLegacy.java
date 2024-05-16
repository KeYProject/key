package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.function.Supplier;

public class DecorateLegacy implements IPromptStrategy<LegacyReasons, Nothing>, IBroadableStrategy<LegacyReasons, Nothing>, LegacyVisitor<Nothing> {
    protected IPromptStrategy<LegacyReasons, Nothing> fallback;

    public DecorateLegacy(IPromptStrategy<LegacyReasons, Nothing> fallback) {
        this.fallback = fallback;
    }

    //region PromptReasons

    public Iterable<Prompt> reason(UnknownReason reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(WrongJML reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(InvalidJava reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(NoJMLInRegion reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(NoJMlInSearchLocations reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(FirstPrompt reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    //endregion

    @Override
    public Iterable<Prompt> apply(LegacyReasons legacyReasons, Nothing o, Supplier<PromptBuilder> newBuilder) {
        return legacyReasons.dispatch(this, o, newBuilder);
    }

    @Override
    public IPromptStrategy<PromptReason, Nothing> broaden() {
        return this::broad_apply;
    }

    public Iterable<Prompt> broad_apply(PromptReason r, Nothing o, Supplier<PromptBuilder> newBuilder) {
        if (r instanceof  LegacyReasons) {
            return apply((LegacyReasons) r, o, newBuilder);
        } else if (fallback instanceof IBroadableStrategy) {
            var broad = ((IBroadableStrategy<LegacyReasons, Nothing>) fallback).broaden();
            return broad.apply(r, o, newBuilder);
        } else {
            return PromptStrategy.NO_PROMPTS;
        }
    }

}
