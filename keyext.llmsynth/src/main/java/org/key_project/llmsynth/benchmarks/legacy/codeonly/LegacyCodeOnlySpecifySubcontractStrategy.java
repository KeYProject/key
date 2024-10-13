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

public class LegacyCodeOnlySpecifySubcontractStrategy extends LegacyCodeOnlySpecifyStrategy implements ISearchStrategy<Nothing>, LegacyVisitor<Nothing> {
    private final ClassInfo clazz;
    private final MethodInfo method;
    private final MethodInfo submethod;
    private final ISearchStrategy<Nothing> fallback;

    public LegacyCodeOnlySpecifySubcontractStrategy(ClassInfo clazz, MethodInfo method, MethodInfo submethod) {
        super(SearchStrategy.getDefault());
        this.clazz = clazz;
        this.method = method;
        this.submethod = submethod;
        this.fallback = SearchStrategy.getDefault();
    }
    public LegacyCodeOnlySpecifySubcontractStrategy(ClassInfo clazz, MethodInfo method, MethodInfo submethod, ISearchStrategy<Nothing> fallback) {
        super(fallback);
        this.clazz = clazz;
        this.method = method;
        this.submethod = submethod;
        this.fallback = fallback;
    }

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

    public Iterable<SearchNode<Nothing>> reason(InvalidJava reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.textln("The provided code is not valid JML");
        b.textln("Only answer with the JML annotation, please refrain from providing the Java code or any natural language information.");
        return List.of(b.build());
    }

    public Iterable<SearchNode<Nothing>> reason(WrongJML reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.text("The provided JML does not solve the task for '").text(submethod.getName()).textln("'.");

        if (reason.getException() != null) {
            b.textln("This might describe the reason:")
                    .textln(reason.getException());
        }
        b.textln("Please use this to fix the following:").textln(reason.getJml());
        b.textln("Only answer with the JML annotation, please refrain from providing the Java code or any natural language information.");
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

    public Iterable<SearchNode<Nothing>> reason(DirectPrompt reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        assert reason.getPreviousReason() instanceof FirstPrompt;
        var b = newBuilder.get();
        b.textln("Given the following Java class:");
        b.classTextInQuotes(clazz);
        b.text("Please provide a JML annotation to the method '")
                .text(submethod.getName().trim())
                .text("' such that the contract specified by '")
                .text(method.getName().trim())
                .textln("' is satisfied.");
        b.textln("Only answer with the JML annotation, please refrain from providing the Java code or any natural language information.");
        return List.of(b.build());
    }
}
