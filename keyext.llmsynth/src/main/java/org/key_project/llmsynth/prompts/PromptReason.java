package org.key_project.llmsynth.prompts;

public class PromptReason {
    PromptReason parent = null;

    // The prompt that was rejected
    PromptResult result = null;
    int depth = 0;

    public PromptReason() {
    }

    public PromptReason(PromptReason parent) {
        this.parent = parent;
        this.depth = parent.depth + 1;
    }

    public int getDepth() {
        return depth;
    }

    public PromptReason getParent() {
        return parent;
    }

    public void setParent(PromptReason parent) {
        this.parent = parent;
        this.depth = parent.depth+1;
    }

    public void setResult(PromptResult r) {
        assert r.getReason() == this;
        this.result = r;
    }

    public Prompt getPrompt() {
        return result.getPrompt();
    }

    public PromptAnswer getAnswer() {
        return result.getAnswer();
    }
}
