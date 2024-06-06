package org.key_project.llmsynth.prompts;

public class PromptAnswer implements PromptMessage {
    private final Prompt prompt;
    private final String answer;

    public PromptAnswer(Prompt prompt, String answer) {
        this.prompt = prompt;
        this.answer = answer;
    }

    public Prompt getPrompt() {
        return prompt;
    }

    public String getContent() {
        return answer;
    }

    @Override
    public PromptType getMessageType() {
        return PromptType.ANSWER;
    }
}
