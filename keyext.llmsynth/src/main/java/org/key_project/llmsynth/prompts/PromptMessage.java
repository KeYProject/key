package org.key_project.llmsynth.prompts;

/**
 * All properties required to correctly use messages with an oracle
 */
public interface PromptMessage {
    /**
     *
     * @return The content of the message
     */
    String getContent();

    /**
     *
     * @return A marker for the purpose of the message
     */
    PromptType getMessageType();
}
