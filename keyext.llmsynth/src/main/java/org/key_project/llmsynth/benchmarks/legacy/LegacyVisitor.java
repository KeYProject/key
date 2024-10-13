package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.prompts.SearchNodeBuilder;
import org.key_project.llmsynth.prompts.reasons.DirectPrompt;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.function.Supplier;

/**
 * Use this to "match" on PromptReasons instead of using instanceof
 * @param <T> User Data type
 */
public interface LegacyVisitor<T> {
    Iterable<SearchNode<T>> reason(UnknownReason reason, T o, Supplier<SearchNodeBuilder<T>> newBuilder);
    Iterable<SearchNode<T>> reason(WrongJML reason, T o, Supplier<SearchNodeBuilder<T>> newBuilder);
    Iterable<SearchNode<T>> reason(InvalidJava reason, T o, Supplier<SearchNodeBuilder<T>> newBuilder);
    Iterable<SearchNode<T>> reason(NoJMLInRegion reason, T o, Supplier<SearchNodeBuilder<T>> newBuilder);
    Iterable<SearchNode<T>> reason(NoJMlInSearchLocations reason, T o, Supplier<SearchNodeBuilder<T>> newBuilder);
    Iterable<SearchNode<T>> reason(FirstPrompt reason, T o, Supplier<SearchNodeBuilder<T>> newBuilder);

    Iterable<SearchNode<T>> reason(DirectPrompt reason, T o, Supplier<SearchNodeBuilder<T>> newBuilder);
}
