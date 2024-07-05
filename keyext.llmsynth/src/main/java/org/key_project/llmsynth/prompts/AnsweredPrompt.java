package org.key_project.llmsynth.prompts;

import java.util.List;

/**
 * A prompt for which an answer has already been set.
 * The BenchmarkRunner will not send it to the oracle.
 */
public class AnsweredPrompt extends Prompt {
    PromptAnswer answer;

    public AnsweredPrompt(Prompt prompt, String answer) {
        super(prompt.elements, prompt.verificator, prompt.promptType, prompt.removeHistory);
        this.answer = new PromptAnswer(this, answer);
    }


    public static Iterable<Prompt> iterableFrom(Prompt prompt, String answer) {
        return List.of(new AnsweredPrompt(prompt, answer));
    }

    public static Iterable<Prompt> iterableFrom(Prompt prompt, PromptMessage answer) {
        // does not retain message type, message type of answer will be ASSISTANT/ANSWER
        return List.of(new AnsweredPrompt(prompt, answer.getContent()));
    }

    /**
     *
     * @return The predetermined answer
     */
    public PromptAnswer getAnswer() {
        return answer;
    }
}
