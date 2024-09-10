package org.key_project.llmsynth.prompts;

import com.fasterxml.jackson.annotation.JsonAutoDetect;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;

/**
 * Represents the answer of a prompt that was once given to an oracle
 */

@JsonAutoDetect(
        fieldVisibility = JsonAutoDetect.Visibility.NONE,
        isGetterVisibility = JsonAutoDetect.Visibility.NONE,
        getterVisibility = JsonAutoDetect.Visibility.NONE,
        setterVisibility = JsonAutoDetect.Visibility.NONE,
        creatorVisibility = JsonAutoDetect.Visibility.NONE
)
public class PromptAnswer implements PromptMessage {
    private final Prompt prompt;
    private final String answer;

    public PromptAnswer(Prompt prompt, String answer) {
        this.prompt = prompt;
        this.answer = answer;
    }

    @JsonProperty("input")
    public String getInput() {
        return this.getPrompt().getContent();
    }

    @JsonProperty("output")
    public String getOutput() {
        return this.answer;
    }

    @JsonProperty("type")
    public String getTypeStr() {
        return getMessageType().name();
    }

    @JsonProperty("keep_history")
    public boolean getKeepsHistory() {
        return !getPrompt().removeHistory;
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
