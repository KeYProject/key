package org.key_project.llmsynth.prompts;

/**
 * A class encoding the verification status of a PromptAnswer.
 * A PromptAnswer may be accepted or rejected.
 */
public class PromptResult {
    private final PromptAnswer answer;
    private final PromptStatus status;
    private final PromptReason reason; // only set, when status == REJECT

    private PromptResult(PromptAnswer answer, PromptStatus status, PromptReason reason) {
        this.answer = answer;
        this.status = status;
        this.reason = reason;
    }

    /**
     *
     * @param a The PromptAnswer to accept
     * @return Creates an accepted PromptResult
     */
    public static PromptResult accept(PromptAnswer a) {
        return new PromptResult(a, PromptStatus.ACCEPTED, null);
    }

    /**
     *
     * @param a The PromptAnswer to reject
     * @param r The reason for rejection
     * @return Creates a rejected PromptResult
     */
    public static PromptResult reject(PromptAnswer a, PromptReason r) {
        return new PromptResult(a, PromptStatus.REJECTED, r);
    }

    /**
     *
     * @return If the prompt was verified successfully.
     */
    public boolean isAccepted() {
        return status == PromptStatus.ACCEPTED;
    }

    /**
     *
     * @return The oacle's answer to the prompt
     */
    public PromptAnswer getAnswer() {
        return answer;
    }

    /**
     *
     * @return The reason verification failed, if applicable
     */
    public PromptReason getReason() {
        return reason;
    }

    /**
     *
     * @return
     */
    public Prompt getPrompt() {
        return getAnswer().getPrompt();
    }
}
