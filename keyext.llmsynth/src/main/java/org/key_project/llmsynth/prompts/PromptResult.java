package org.key_project.llmsynth.prompts;

public class PromptResult {
    private final PromptAnswer answer;
    private final PromptStatus status;
    private final PromptReason reason; // only set, when status == REJECT

    private PromptResult(PromptAnswer answer, PromptStatus status, PromptReason reason) {
        this.answer = answer;
        this.status = status;
        this.reason = reason;
    }

    public static PromptResult accept(PromptAnswer a) {
        return new PromptResult(a, PromptStatus.ACCEPTED, null);
    }

    public static PromptResult reject(PromptAnswer a, PromptReason r) {
        return new PromptResult(a, PromptStatus.REJECTED, r);
    }

    public boolean isAccepted() {
        return status == PromptStatus.ACCEPTED;
    }

    public PromptAnswer getAnswer() {
        return answer;
    }

    public PromptReason getReason() {
        return reason;
    }

    public Prompt getPrompt() {
        return getAnswer().getPrompt();
    }
}
