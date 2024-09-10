package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.prompts.*;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.List;
import java.util.function.Supplier;

// todo: make this not inherit from DecorateLegacy
public class LegacySpecifyLoopinvariantStrategy extends DecorateLegacy<Nothing> implements ISearchStrategy<Nothing>, LegacyVisitor<Nothing> {
    private final ClassInfo clazz;
    private final MethodInfo method;

    public LegacySpecifyLoopinvariantStrategy(ClassInfo clazz, MethodInfo method) {
        super(SearchStrategy.getDefault());
        this.clazz = clazz;
        this.method = method;
    }

    public LegacySpecifyLoopinvariantStrategy(ClassInfo clazz, MethodInfo method, ISearchStrategy<Nothing> fallback) {
        super(fallback);
        this.clazz = clazz;
        this.method = method;
    }

    @Override
    public Iterable<SearchNode<Nothing>> reason(UnknownReason reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("Could you rephrase your solution? Please provide a valid JML loop invariant.");
        if (reason.getException() != null) {
            b.textln("This might describe the reason why change is required:")
                    .textln(reason.getException().getMessage());
        }
        return List.of(b.build());
    }

    @Override
    public Iterable<SearchNode<Nothing>> reason(WrongJML reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.text("The provided JML loop invariant does not solve the task for '").text(method.getName()).textln("'.");

        if (reason.getException() != null) {
            b.textln("This might describe the reason:")
                    .textln(reason.getException().getMessage());
        }
        b.textln("Please use this to fix the following:").textln(reason.getJml());
        return List.of(b.build());
    }

    @Override
    public Iterable<SearchNode<Nothing>> reason(InvalidJava reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("The provided code is not a valid loop-invariant");
        return List.of(b.build());
    }

    @Override
    public Iterable<SearchNode<Nothing>> reason(NoJMLInRegion reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.text("Please write the loop invariant directly above the first loop construct of '")
                .text(method.getName()).textln("'");
        return List.of(b.build());
    }

    @Override
    public Iterable<SearchNode<Nothing>> reason(NoJMlInSearchLocations reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.text("Please write the loop invariant directly above the first loop construct of '")
                .text(method.getName()).textln("'");
        return List.of(b.build());
    }

    @Override
    public Iterable<SearchNode<Nothing>> reason(FirstPrompt reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("Given the following Java class:");
        b.classTextInQuotes(clazz);
        b.text("Please provide a loop invariant for the first loop construct of the method '")
                .text(method.getName())
                .textln("'");
        return List.of(b.build());
    }
}
