package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.prompts.IPromptStrategy;
import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptBuilder;
import org.key_project.llmsynth.prompts.PromptReason;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.function.Supplier;

public class DecorateLegacy implements IPromptStrategy<LegacyReasons, String>, LegacyVisitor<String> {
    IPromptStrategy<LegacyReasons, String> fallback;

    public DecorateLegacy(IPromptStrategy<LegacyReasons, String> fallback) {
        this.fallback = fallback;
    }

    //region PromptReasons

    public Iterable<Prompt> reason(UnknownReason reason, String o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(BadProof reason, String o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(WrongJML reason, String o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(InvalidJava reason, String o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(NoJMLInRegion reason, String o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(NoJMlInSearchLocations reason, String o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    public Iterable<Prompt> reason(FirstPrompt reason, String o, Supplier<PromptBuilder> newBuilder) {
        return fallback.apply(reason, o, newBuilder);
    }

    //endregion

    @Override
    public Iterable<Prompt> apply(LegacyReasons legacyReasons, String o, Supplier<PromptBuilder> newBuilder) {
        return legacyReasons.dispatch(this, o, newBuilder);
    }

    @Override
    public IPromptStrategy<PromptReason, String> broaden() {
        return this::broad_apply;
    }

    public Iterable<Prompt> broad_apply(PromptReason r, String o, Supplier<PromptBuilder> newBuilder) {
        if (r instanceof  LegacyReasons) {
            return apply((LegacyReasons) r, o, newBuilder);
        } else {
            return fallback.broaden().apply(r, o, newBuilder);
        }
    }

}
