package org.key_project.llmsynth.benchmarks.legacy.standard;

import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.benchmarks.legacy.DecorateLegacy;
import org.key_project.llmsynth.prompts.ISearchStrategy;
import org.key_project.llmsynth.prompts.SearchNodeBuilder;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.List;
import java.util.function.Supplier;

public abstract class LegacySpecifyStrategy extends DecorateLegacy<Nothing> {
    public LegacySpecifyStrategy(ISearchStrategy<Nothing> fallback) {
        super(fallback);
    }

    public final Iterable<SearchNode<Nothing>> reason(FirstPrompt reason, Nothing o, Supplier<SearchNodeBuilder<Nothing>> newBuilder) {
        var b = newBuilder.get();
        b.skipVerification();
        b.asSystemPrompt();
        b.isAnswered();
        b.text("You are an assistant for JML annotation.\n" +
                "In the first message of this conversation, you are provided with a Java class with partial JML annotation.\n" +
                "Additionally, you are provided with natural language instructions that describe the task to be completed.\n" +
                "JML annotation is a complicated task, but you are very capable and a perfect fit for this job.\n" +
                "First, think step by step: What does the code do? What is the context in which the code is executed? What variables are relevant?\n" +
                "Draft a behavioral description in natural language.\n" +
                "Subsequently, translate this description into JML annotation.\n" +
                "You should only provide the JML annotation and not the Java code.\n" +
                "We will then use the KeY verification system to check if the JML annotation is correct.\n" +
                "If the program verification fails, you will be provided with information about the failure and asked to correct the JML annotation.\n" +
                "Always add the JML keyword `normal_behavior` to the contract -- this guarantees that no exceptions are being thrown.\n" +
                "Your answers should always have the following format where the the <X> is substituted by the JML annotation suggested by you:\n" +
                "<your natural language reasoning>\n" +
                "```\n" +
                "/*@ <X>\n" +
                "*/\n" +
                "```");
        return List.of(b.build());
    }
}
