package org.key_project.llmsynth.benchmarks.legacy.natural;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.benchmarks.legacy.*;
import org.key_project.llmsynth.prompts.ISearchStrategy;
import org.key_project.llmsynth.prompts.PromptReason;
import org.key_project.llmsynth.prompts.SearchNodeBuilder;
import org.key_project.llmsynth.prompts.SearchStrategy;
import org.key_project.llmsynth.prompts.reasons.DirectPrompt;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.List;
import java.util.function.Supplier;

// todo: make this not inherit from DecorateLegacy
public class LegacySpecifyNaturalSubcontractStrategy extends LegacySpecifyNaturalStrategy implements ISearchStrategy<Nothing>, LegacyVisitor<Nothing> {
    private final ClassInfo clazz;
    private final MethodInfo method;
    private final MethodInfo submethod;
    private final ISearchStrategy<Nothing> fallback;

    public LegacySpecifyNaturalSubcontractStrategy(ClassInfo clazz, MethodInfo method, MethodInfo submethod) {
        super(SearchStrategy.getDefault());
        this.clazz = clazz;
        this.method = method;
        this.submethod = submethod;
        this.fallback = SearchStrategy.getDefault();
    }
    public LegacySpecifyNaturalSubcontractStrategy(ClassInfo clazz, MethodInfo method, MethodInfo submethod, ISearchStrategy<Nothing> fallback) {
        super(fallback);
        this.clazz = clazz;
        this.method = method;
        this.submethod = submethod;
        this.fallback = fallback;
    }

    public Iterable<SearchNode<Nothing>> reason(UnknownReason reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.skipVerification();
        b.textln("There was an unknown problem with the JML annotation.");
        if (reason.getException() != null) {
            b.textln("This might describe the reason why change is required:")
                    .textln(reason.getException());
        }
        b.textln("Please explain in natural language why the previous answer is incorrect and provide ideas in natural language how this might be fixed.");
        b.textln("Do not write any JML yet, just describe the method's behaviour in natural language.");
        return List.of(b.build());
    }

    public Iterable<SearchNode<Nothing>> reason(InvalidJava reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.skipVerification();
        b.textln("The provided code is not valid JML");
        if (reason.getException() != null) {
            b.textln("This might describe the reason why change is required:")
                    .textln(reason.getException());
        }
        b.textln("Please explain in natural language why the previous answer is incorrect and provide ideas in natural language how this might be fixed.");
        b.textln("Do not write any JML yet, just describe the method's behaviour in natural language.");
        return List.of(b.build());
    }

    public Iterable<SearchNode<Nothing>> reason(WrongJML reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.skipVerification();
        b.text("The provided JML does not solve the task for '").text(submethod.getName()).text("' and '")
                .text(method.getName()).textln("'.");

        if (reason.getException() != null) {
            b.textln("This might describe the reason:")
                    .textln(reason.getException())
                    .newln();
        }
        //b.textln("Please use this to fix the following:").textln(reason.getJml());
        b.textln("Please explain in natural language why the previous answer is incorrect and provide ideas in natural language how this might be fixed.");
        b.textln("Do not write any JML yet, just describe the method's behaviour in natural language.");
        return List.of(b.build());
    }

    public Iterable<SearchNode<Nothing>> reason(NoJMLInRegion reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("Your previous answer did not contain any JML annotations.");
        b.textln("Please write some JML for the method '" + submethod.getName() + "'.");
        b.textln("Note the contract also has to be satisfied w.r.t. the implementation of the method '" + method.getName() + "'.");
        b.text("Please write your JML answer directly in a block of the following form:\n"
                + "```\n" +
                "/*@ <X>\n" +
                "*/\n" +
                "```");
        return List.of(b.build());
    }

    public Iterable<SearchNode<Nothing>> reason(NoJMlInSearchLocations reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("Your previous answer did not contain any JML annotations.");
        b.textln("Please write some JML for the method '" + submethod.getName() + "'.");
        b.textln("Note the contract also has to be satisfied w.r.t. the implementation of the method '" + method.getName() + "'.");
        b.text("Please write your JML answer directly in a block of the following form:\n"
                + "```\n" +
                "/*@ <X>\n" +
                "*/\n" +
                "```");
        return List.of(b.build());
    }

    @Override
    public Iterable<SearchNode<Nothing>> reason(DirectPrompt reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        if (reason.getPreviousReason() instanceof FirstPrompt) {
            var b = newBuilder.get();
            b.skipVerification();
            b.textln("Given the following Java class:");
            b.classTextInQuotes(clazz);
            b.text("We want to generate a JML specification for the method ")
                    .text(submethod.getName())
                    .text("' such that the contract specified by '")
                    .text(method.getName().trim())
                    .textln("' is satisfied.");
            b.textln("As a first step, please draft a natural language description of the method's behaviour.");
            b.textln("Describe any preconditions, postconditions, and invariants that you think are relevant.");
            b.textln("Also describe any side effects and edge cases that you think are important.");
            b.textln("Do not write any JML yet, just describe the method's behaviour in natural language.");
            return List.of(b.build());
        } else {
            return this.promptJMLGeneration(reason.getPreviousReason(), o, newBuilder);
        }
    }

    public Iterable<SearchNode<Nothing>> promptJMLGeneration(PromptReason reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("Great, based on your natural language description, we now need to generate a JML annotation for the method '" + method.getName() + "'.");
        b.textln("Please write a JML annotation for the method '" + method.getName() + "' that correctly captures the behavior of the implementation.");
        b.text("Please write your JML answer directly in a block of the following form:\n"
                + "<your natural language reasoning>\n"
                + "```\n" +
                "/*@ <X>\n" +
                "*/\n" +
                "```");
        return List.of(b.build());
    }
}
