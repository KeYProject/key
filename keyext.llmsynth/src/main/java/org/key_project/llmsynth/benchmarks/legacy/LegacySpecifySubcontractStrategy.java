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
public class LegacySpecifySubcontractStrategy extends DecorateLegacy<Nothing> implements ISearchStrategy<Nothing>, LegacyVisitor<Nothing> {
    private final ClassInfo clazz;
    private final MethodInfo method;
    private final MethodInfo submethod;
    private final ISearchStrategy<Nothing> fallback;

    public LegacySpecifySubcontractStrategy(ClassInfo clazz, MethodInfo method, MethodInfo submethod) {
        super(SearchStrategy.getDefault());
        this.clazz = clazz;
        this.method = method;
        this.submethod = submethod;
        this.fallback = SearchStrategy.getDefault();
    }
    public LegacySpecifySubcontractStrategy(ClassInfo clazz, MethodInfo method, MethodInfo submethod, ISearchStrategy<Nothing> fallback) {
        super(fallback);
        this.clazz = clazz;
        this.method = method;
        this.submethod = submethod;
        this.fallback = fallback;
    }

    public Iterable<SearchNode<Nothing>> reason(UnknownReason reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("Could you rephrase your solution? Please only provide the JML contract.");
        if (reason.getException() != null) {
            b.textln("This might describe the reason why change is required:")
                    .textln(reason.getException().getMessage());
        }
        return List.of(b.build());
    }

    public Iterable<SearchNode<Nothing>> reason(InvalidJava reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("The provided code is not valid JML");
        return List.of(b.build());
    }

    public Iterable<SearchNode<Nothing>> reason(WrongJML reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.text("The provided JML does not solve the task for '").text(submethod.getName()).textln("'.");

        if (reason.getException() != null) {
            b.textln("This might describe the reason:")
                    .textln(reason.getException().getMessage());
        }
        b.textln("Please use this to fix the following:").textln(reason.getJml());
        return List.of(b.build());
    }

    public Iterable<SearchNode<Nothing>> reason(NoJMLInRegion reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("Please write some JML for the method '" + submethod.getName() + "' that solves the task into a code region");
        return List.of(b.build());
    }

    public Iterable<SearchNode<Nothing>> reason(NoJMlInSearchLocations reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.text("Please write the JML directly above the method declaration of '")
                .text(method.getName()).textln("'");
        return List.of(b.build());
    }

    @Override
    public Iterable<SearchNode<Nothing>> reason(FirstPrompt reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
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
}
