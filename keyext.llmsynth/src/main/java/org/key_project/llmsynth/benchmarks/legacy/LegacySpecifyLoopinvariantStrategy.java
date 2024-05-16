package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.List;
import java.util.function.Supplier;

public class LegacySpecifyLoopinvariantStrategy implements IPromptStrategy<LegacyReasons, Nothing>, IBroadableStrategy<LegacyReasons, Nothing>, LegacyVisitor<Nothing> {
    private final ClassInfo clazz;
    private final MethodInfo method;
    private final IPromptStrategy<PromptReason, Nothing> fallback;

    public LegacySpecifyLoopinvariantStrategy(ClassInfo clazz, MethodInfo method) {
        this.clazz = clazz;
        this.method = method;
        this.fallback = PromptStrategy.getDefault();
    }
    public LegacySpecifyLoopinvariantStrategy(ClassInfo clazz, MethodInfo method, IPromptStrategy<PromptReason, Nothing> fallback) {
        this.clazz = clazz;
        this.method = method;
        this.fallback = fallback;
    }

    @Override
    public Iterable<Prompt> reason(UnknownReason reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.textln("Could you rephrase your solution? Please provide a valid JML loop invariant.");
        if (reason.getException() != null) {
            b.textln("This might describe the reason why change is required:")
                    .textln(reason.getException().getMessage());
        }
        return List.of(b.build());
    }

    @Override
    public Iterable<Prompt> reason(WrongJML reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.text("The provided JML loop invariant does not solve the task for '").text(method.getName()).textln("'.");

        if (reason.getException() != null) {
            b.textln("This might describe the reason:")
                    .textln(reason.getException().getMessage())
                    .newln();
        }
        b.textln("Please use this to fix the following:").textln(reason.getJml());
        return List.of(b.build());
    }

    @Override
    public Iterable<Prompt> reason(InvalidJava reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.textln("The provided code is not a valid loop-invariant");
        return List.of(b.build());
    }

    @Override
    public Iterable<Prompt> reason(NoJMLInRegion reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.text("Please write the loop invariant directly above the first loop construct of '")
                .text(method.getName()).textln("'");
        return List.of(b.build());
    }

    @Override
    public Iterable<Prompt> reason(NoJMlInSearchLocations reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.text("Please write the loop invariant directly above the first loop construct of '")
                .text(method.getName()).textln("'");
        return List.of(b.build());
    }

    @Override
    public Iterable<Prompt> reason(FirstPrompt reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.textln("Given the following Java class:");
        b.classTextInQuotes(clazz);
        b.text("Please provide a loop invariant for the first loop construct of the method '")
                .text(method.getName())
                .textln("'");
        return List.of(b.build());
    }

    @Override
    public IPromptStrategy<PromptReason, Nothing> broaden() {
        return this::broad_apply;
    }

    @Override
    public Iterable<Prompt> apply(LegacyReasons reason, Nothing nothing, Supplier<PromptBuilder> newBuilder) {
        return reason.dispatch(this, nothing, newBuilder);
    }

    public Iterable<Prompt> broad_apply(PromptReason r, Nothing o, Supplier<PromptBuilder> newBuilder) {
        if (r instanceof  LegacyReasons) {
            return apply((LegacyReasons) r, o, newBuilder);
        } else {
            return fallback.apply(r, o, newBuilder);
        }
    }
}
