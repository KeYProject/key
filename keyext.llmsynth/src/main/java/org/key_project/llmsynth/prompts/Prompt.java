package org.key_project.llmsynth.prompts;

import org.key_project.llmsynth.prompts.reasons.DirectPrompt;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

public class Prompt implements PromptMessage {
    protected final List<PromptElement> elements; // = new ArrayList<>();
    protected String promptString; // = null;
    protected final boolean removeHistory; // only useful for normal search-tre operations, should be in subclass, and injected by a prompt builder
    protected final PromptType promptType;

    protected final Function<PromptAnswer, PromptResult> verificator;

    Prompt(List<PromptElement> elements, Function<PromptAnswer, PromptResult> verificator, PromptType promptType, boolean removeHistory) {
        this.elements = elements;
        this.verificator = verificator;
        this.promptType = promptType;
        this.removeHistory = removeHistory;
    }

    public void print(PrintWriter pw) {
        for (var e : elements) {
            e.print(pw);
        }
    }

    // TODO: the verificator shouldn't really be here, however for now it will stay
    // on the flip side: if the same prompt is run through the oracle multiple times, it is fine here, i think
    public PromptResult verifyAnswer(PromptAnswer answer) {
        return verificator.apply(answer);
    }

    public boolean hasRemoveHistoryFlag() {
        return removeHistory;
    }

    @Override
    public String toString() {
        if (promptString == null) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);;
            elements.forEach(e -> e.print(pw));
            promptString = sw.toString();
        }
        return promptString;
    }

    @Override
    public String getContent() {
        return this.toString();
    }

    @Override
    public PromptType getMessageType() {
        return promptType;
    }

    public static Prompt from(PromptType typ, String s) {
        return new Prompt(List.of(p -> p.println(s)), a -> PromptResult.reject(a, new DirectPrompt()), typ, false);
    }
}
