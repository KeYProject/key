package org.key_project.llmsynth.prompts;

/**
 * All properties required to correctly use messages with an oracle
 */
public class PromptMessage {
    final String content;
    final PromptType type;

    public PromptMessage(PromptType type, String content) {
        this.type = type;
        this.content = content;
    }

    /**
     *
     * @return The content of the message
     */
    public String getContent() {
        return content;
    }

    /**
     *
     * @return A marker for the purpose of the message
     */
    public PromptType getMessageType() {
        return type;
    }

}
