package org.key_project.llmsynth.prompts;

import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonInclude.Include;

/**
 * A class encoding the verification status of a Prompt.
 * A Prompt may be accepted or rejected.
 */
public class VerificationResult {
    @JsonInclude
    private final Prompt prompt;
    @JsonInclude
    private final PromptStatus status;

    @JsonInclude(Include.NON_NULL)
    private final PromptReason reason; // only set, when status == REJECT

    private VerificationResult(Prompt prompt, PromptStatus status, PromptReason reason) {
        this.prompt = prompt;
        this.status = status;
        this.reason = reason;
    }

    /**
     *
     * @param a The PromptAnswer to accept
     * @return Creates an accepted PromptResult
     */
    public static VerificationResult accept(Prompt a) {
        return new VerificationResult(a, PromptStatus.ACCEPTED, null);
    }

    /**
     *
     * @param a The PromptAnswer to reject
     * @param r The reason for rejection
     * @return Creates a rejected PromptResult
     */
    public static VerificationResult reject(Prompt a, PromptReason r) {
        return new VerificationResult(a, PromptStatus.REJECTED, r);
    }

    /**
     *
     * @return If the prompt was verified successfully.
     */
    @JsonIgnore
    public boolean isAccepted() {
        return status == PromptStatus.ACCEPTED;
    }

    public PromptStatus getStatus() {
        return status;
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
     * @return The prompt that was sent to the oracle
     */
    public Prompt getPrompt() {
        return prompt;
    }
}
