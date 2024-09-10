package org.key_project.llmsynth.prompts.reasons;

import org.key_project.llmsynth.prompts.PromptReason;

/**
 * The last prompt was not verified, and instead its result is directly used here
 */
public class DirectPrompt extends PromptReason {
    public DirectPrompt() {
        super("direct prompt");
    }
}
