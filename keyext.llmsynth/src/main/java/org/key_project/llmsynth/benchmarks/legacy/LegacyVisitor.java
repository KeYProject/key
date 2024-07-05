package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptBuilder;
import org.key_project.llmsynth.prompts.reasons.FirstPrompt;

import java.util.function.Supplier;

/**
 * Use this to "match" on PromptReasons instead of using instanceof
 * @param <T> User Data type
 */
public interface LegacyVisitor<T> {
    Iterable<Prompt> reason(UnknownReason reason, T o, Supplier<PromptBuilder> newBuilder);
    Iterable<Prompt> reason(WrongJML reason, T o, Supplier<PromptBuilder> newBuilder);
    Iterable<Prompt> reason(InvalidJava reason, T o, Supplier<PromptBuilder> newBuilder);
    Iterable<Prompt> reason(NoJMLInRegion reason, T o, Supplier<PromptBuilder> newBuilder);
    Iterable<Prompt> reason(NoJMlInSearchLocations reason, T o, Supplier<PromptBuilder> newBuilder);
    Iterable<Prompt> reason(FirstPrompt reason, T o,  Supplier<PromptBuilder> newBuilder);
}
