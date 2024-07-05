package org.key_project.llmsynth.prompts;

/**
 * Represents the answer of a prompt that was once given to an oracle
 */
public class PromptAnswer implements PromptMessage {
    private final Prompt prompt;
    private final String answer;

    public PromptAnswer(Prompt prompt, String answer) {
        this.prompt = prompt;
        this.answer = answer;
    }

    /**
     *
     * @return The prompt originally sent to the oracle
     */
    public Prompt getPrompt() {
        return prompt;
    }

    /**
     *
     * @return The answer of the prompt
     */
    public String getContent() {
        return answer;
    }

    @Override
    public PromptType getMessageType() {
        return PromptType.ANSWER;
    }
}
