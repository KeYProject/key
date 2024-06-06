package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.List;
import java.util.function.Supplier;

public class LegacySpecifySubcontractStrategy implements IPromptStrategy<Nothing>, LegacyVisitor<Nothing> {
    private final ClassInfo clazz;
    private final MethodInfo method;
    private final MethodInfo submethod;
    private final IPromptStrategy<Nothing> fallback;

    public LegacySpecifySubcontractStrategy(ClassInfo clazz, MethodInfo method, MethodInfo submethod) {
        this.clazz = clazz;
        this.method = method;
        this.submethod = submethod;
        this.fallback = PromptStrategy.getDefault();
    }
    public LegacySpecifySubcontractStrategy(ClassInfo clazz, MethodInfo method, MethodInfo submethod, IPromptStrategy<Nothing> fallback) {
        this.clazz = clazz;
        this.method = method;
        this.submethod = submethod;
        this.fallback = fallback;
    }

    public Iterable<Prompt> reason(UnknownReason reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.textln("Could you rephrase your solution? Please only provide the JML contract.");
        if (reason.getException() != null) {
            b.textln("This might describe the reason why change is required:")
                    .textln(reason.getException().getMessage());
        }
        return List.of(b.build());
    }

    public Iterable<Prompt> reason(InvalidJava reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.textln("The provided code is not valid JML");
        return List.of(b.build());
    }

    public Iterable<Prompt> reason(WrongJML reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.text("The provided JML does not solve the task for '").text(submethod.getName()).textln("'.");

        if (reason.getException() != null) {
            b.textln("This might describe the reason:")
                    .textln(reason.getException().getMessage());
        }
        b.textln("Please use this to fix the following:").textln(reason.getJml());
        return List.of(b.build());
    }

    public Iterable<Prompt> reason(NoJMLInRegion reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.textln("Please write some JML for the method '" + submethod.getName() + "' that solves the task into a code region");
        return List.of(b.build());
    }

    public Iterable<Prompt> reason(NoJMlInSearchLocations reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.text("Please write the JML directly above the method declaration of '")
                .text(method.getName()).textln("'");
        return List.of(b.build());
    }

    @Override
    public Iterable<Prompt> reason(FirstPrompt reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.textln("Given the following Java class:");
        b.classTextInQuotes(clazz);
        b.text("Please provide a JML annotation to the method '")
                .text(submethod.getName().trim())
                .text("' such that the contract specified by '")
                .text(method.getName().trim())
                .textln("' is satisfied.");
        return List.of(b.build());
    }

    public Iterable<Prompt> apply(PromptReason r, Nothing o, Supplier<PromptBuilder> newBuilder) {
        if (r instanceof  LegacyReasons) {
            return ((LegacyReasons)r).dispatch(this, o, newBuilder);
        } else {
            return fallback.apply(r, o, newBuilder);
        }
    }
}
