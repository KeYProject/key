package org.key_project.llmsynth.prompts;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

public class Prompt {
    private final List<PromptElement> elements; // = new ArrayList<>();
    private String promptString; // = null;
    private boolean removeHistory;

    private final Function<PromptAnswer, PromptResult> verificator;

    Prompt(List<PromptElement> elements, Function<PromptAnswer, PromptResult> verificator, boolean removeHistory) {
        this.elements = elements;
        this.verificator = verificator;
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
}
