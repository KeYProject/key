package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.function.Supplier;

public class LegacySpecifyTopLevel implements IPromptStrategy<LegacyReasons, String>, LegacyVisitor<String> {
    // - UNKNOWN_FATAL todo: not handled, as this should lead to a cancellation of the benchmark
    IPromptStrategy<PromptReason, String> fallback = PromptStrategy.getDefault();

    public LegacySpecifyTopLevel() {}
    public LegacySpecifyTopLevel(IPromptStrategy<PromptReason, String> fallback) {
        this.fallback = fallback;
    }

    //region PromptReasons

    public Iterable<Prompt> reason(UnknownReason reason, String o, Supplier<PromptBuilder> newBuilder) {
        return PromptStrategy.NO_PROMPTS;
    }

    public Iterable<Prompt> reason(BadProof reason, String o, Supplier<PromptBuilder> newBuilder) {
        return PromptStrategy.NO_PROMPTS;
    }

    public Iterable<Prompt> reason(WrongJML reason, String o, Supplier<PromptBuilder> newBuilder) {
        return PromptStrategy.NO_PROMPTS;
    }

    public Iterable<Prompt> reason(InvalidJava reason, String o, Supplier<PromptBuilder> newBuilder) {
        return PromptStrategy.NO_PROMPTS;
    }

    public Iterable<Prompt> reason(NoJMLInRegion reason, String o, Supplier<PromptBuilder> newBuilder) {
        return PromptStrategy.NO_PROMPTS;
    }

    public Iterable<Prompt> reason(NoJMlInSearchLocations reason, String o, Supplier<PromptBuilder> newBuilder) {
        return PromptStrategy.NO_PROMPTS;
    }

    public Iterable<Prompt> reason(FirstPrompt reason, String o, Supplier<PromptBuilder> newBuilder) {
        return PromptStrategy.NO_PROMPTS;
    }

    //endregion

    @Override
    public Iterable<Prompt> apply(LegacyReasons legacyReasons, String o, Supplier<PromptBuilder> newBuilder) {
        return legacyReasons.dispatch(this, o, newBuilder);
    }

    public Iterable<Prompt> broad_apply(PromptReason r, String o, Supplier<PromptBuilder> newBuilder) {
        if (r instanceof  LegacyReasons) {
            return apply((LegacyReasons) r, o, newBuilder);
        } else {
            return fallback.apply(r, o, newBuilder);
        }
    }

    @Override
    public IPromptStrategy<PromptReason, String> broaden() {
        return this::broad_apply;
    }

    @Override
    public Class<LegacyReasons> getReasonType() {
        return LegacyReasons.class;
    }
}
