package org.key_project.llmsynth.benchmarks.legacy.codeonly;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.benchmarks.legacy.*;
import org.key_project.llmsynth.prompts.ISearchStrategy;
import org.key_project.llmsynth.prompts.SearchNodeBuilder;
import org.key_project.llmsynth.prompts.SearchStrategy;
import org.key_project.llmsynth.prompts.reasons.DirectPrompt;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.List;
import java.util.function.Supplier;

public class LegacyCodeOnlySpecifyLoopinvariantStrategy extends LegacyCodeOnlySpecifyStrategy implements ISearchStrategy<Nothing>, LegacyVisitor<Nothing> {
    private final ClassInfo clazz;
    private final MethodInfo method;

    public LegacyCodeOnlySpecifyLoopinvariantStrategy(ClassInfo clazz, MethodInfo method) {
        super(SearchStrategy.getDefault());
        this.clazz = clazz;
        this.method = method;
    }

    public LegacyCodeOnlySpecifyLoopinvariantStrategy(ClassInfo clazz, MethodInfo method, ISearchStrategy<Nothing> fallback) {
        super(fallback);
        this.clazz = clazz;
        this.method = method;
    }

    @Override
    public Iterable<SearchNode<Nothing>> reason(UnknownReason reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("There was an unknown problem with the JML annotation.");
        if (reason.getException() != null) {
            b.textln("This might describe the reason why change is required:")
                    .textln(reason.getException());
        }
        b.textln("Please repair your solution and provide a valid JML annotation.");
        b.textln("Only answer with the JML annotation, please refrain from providing the Java code or any natural language information.");
        return List.of(b.build());
    }

    @Override
    public Iterable<SearchNode<Nothing>> reason(WrongJML reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.text("The provided JML loop invariant does not solve the task for '").text(method.getName()).textln("'.");

        if (reason.getException() != null) {
            b.textln("This might describe the reason:")
                    .textln(reason.getException());
        }
        b.textln("Please use this to fix the following:").textln(reason.getJml());
        b.textln("Only answer with the JML annotation, please refrain from providing the Java code or any natural language information.");
        return List.of(b.build());
    }

    @Override
    public Iterable<SearchNode<Nothing>> reason(InvalidJava reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("The provided code is not a valid loop-invariant");
        b.textln("Only answer with the JML annotation, please refrain from providing the Java code or any natural language information.");
        return List.of(b.build());
    }

    public Iterable<SearchNode<Nothing>> reason(NoJMLInRegion reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("Your previous answer did not contain any JML annotations.");
        b.textln("Please directly provide the loop invariant for the annotated loop in method "+method.getName()+" within a code block");
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
        b.textln("Please directly provide the loop invariant for the annotated loop in method "+method.getName()+" within a code block");
        b.text("Please write your JML answer directly in a block of the following form:\n"
                + "```\n" +
                "/*@ <X>\n" +
                "*/\n" +
                "```");
        return List.of(b.build());
    }

    public Iterable<SearchNode<Nothing>> reason(DirectPrompt reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        assert reason.getPreviousReason() instanceof FirstPrompt;
        var b = newBuilder.get();
        b.textln("Given the following Java class:");
        b.classTextInQuotes(clazz);
        b.text("Please provide a loop invariant for the first loop construct of the method '")
                .text(method.getName())
                .textln("'");
        b.textln("Only answer with the JML annotation, please refrain from providing the Java code or any natural language information.");
        return List.of(b.build());
    }
}