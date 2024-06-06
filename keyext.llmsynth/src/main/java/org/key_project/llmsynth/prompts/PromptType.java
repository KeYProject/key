package org.key_project.llmsynth.prompts;

public enum PromptType {
    USER,
    SYSTEM,
    ASSISTANT,
    ;
    public static PromptType ANSWER = PromptType.ASSISTANT;
}
