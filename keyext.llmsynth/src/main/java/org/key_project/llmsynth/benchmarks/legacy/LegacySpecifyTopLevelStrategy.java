package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.List;
import java.util.function.Supplier;

public class LegacySpecifyTopLevelStrategy implements IPromptStrategy<Nothing>, LegacyVisitor<Nothing> {
    IPromptStrategy<Nothing> fallback;
    MethodInfo method;
    ClassInfo clazz;

    public LegacySpecifyTopLevelStrategy(ClassInfo clazz, MethodInfo method) {
        this.clazz = clazz;
        this.method = method;
        this.fallback = PromptStrategy.getDefault();
    }
    public LegacySpecifyTopLevelStrategy(ClassInfo clazz, MethodInfo method, IPromptStrategy<Nothing> fallback) {
        this.clazz = clazz;
        this.method = method;
        this.fallback = fallback;
    }

    //region PromptReasons

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
        b.text("The provided JML does not solve the task for '").text(method.getName()).textln("'.");

        if (reason.getException() != null) {
            b.textln("This might describe the reason:")
                    .textln(reason.getException().getMessage())
                    .newln();
        }
        b.textln("Please use this to fix the following:").textln(reason.getJml());
        return List.of(b.build());
    }

    public Iterable<Prompt> reason(NoJMLInRegion reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.textln("Please write some JML for the method '" + method.getName() + "' that solves the task into a code region");
        return List.of(b.build());
    }

    public Iterable<Prompt> reason(NoJMlInSearchLocations reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.text("Please write the JML directly above the method declaration of '")
                .text(method.getName()).textln("'");
        return List.of(b.build());
    }

    public Iterable<Prompt> reason(FirstPrompt reason, Nothing o, Supplier<PromptBuilder> newBuilder) {
        var b = newBuilder.get();
        b.textln("Given the following Java class:");
        b.classTextInQuotes(clazz);
        b.text("Please provide a JML annotation to the method '")
         .text(method.getName())
         .textln("' such that its behaviour is correctly reflected as a method contract.");
        return List.of(b.build());
    }

    //endregion

    @Override
    public Iterable<Prompt> apply(PromptReason r, Nothing o, Supplier<PromptBuilder> newBuilder) {
        if (r instanceof  LegacyReasons) {
            return ((LegacyReasons)r).dispatch(this, o, newBuilder);
        } else {
            return fallback.apply(r, o, newBuilder);
        }
    }

}
