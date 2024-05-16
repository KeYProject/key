package org.key_project.llmsynth.prompts;

import org.key_project.llmsynth.benchmarks.legacy.LegacyReasons;

public interface IBroadableStrategy<TReason extends PromptReason, TUserData> extends IPromptStrategy<TReason, TUserData> {
    IPromptStrategy<PromptReason, TUserData> broaden();
}
