package org.key_project.llmsynth.prompts;

/**
 * An indicator of what purpose a PromptMessage holds
 */
public enum PromptType {
    /**
     * The content is a message that is supposed to be answered
     */
    USER,
    /**
     * The content is a message that is not supposed ot be answered, but still impacts the behaviour of the following prompts
     */
    SYSTEM,
    /**
     * The content is the answer to a message
     */
    ASSISTANT;
    /**
     * The content is the answer to a message (alternative to ASSISTANT)
     */
    public static PromptType ANSWER = PromptType.ASSISTANT;
}
