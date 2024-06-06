package org.key_project.llmsynth.prompts;

public interface PromptMessage {
    String getContent();
    PromptType getMessageType();
}
