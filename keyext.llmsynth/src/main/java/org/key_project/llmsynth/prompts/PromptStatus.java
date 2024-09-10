package org.key_project.llmsynth.prompts;

/**
 * The verification status of a Prompt
 */
public enum PromptStatus {
    /**
     * Verification has not yet been tried
     */
    UNKNOWN,
    /**
     * The answer to the prompt was accepted as a solution
     */
    ACCEPTED,
    /**
     * The answer to the prompt was rejected as a solution
     */
    REJECTED
}
