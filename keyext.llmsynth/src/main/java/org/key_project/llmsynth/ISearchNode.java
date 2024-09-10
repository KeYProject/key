package org.key_project.llmsynth;

import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptReason;

public interface ISearchNode {
    ISearchNode getParent();
    PromptReason getReason();
    Prompt getPrompt();
    boolean useForHistory();
}
