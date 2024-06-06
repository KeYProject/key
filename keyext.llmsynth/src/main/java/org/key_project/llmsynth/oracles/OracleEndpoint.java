package org.key_project.llmsynth.oracles;

import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptAnswer;
import org.key_project.llmsynth.prompts.PromptMessage;

import java.util.List;

public interface OracleEndpoint {
    PromptMessage ask(List<PromptMessage> prompts);

    default PromptMessage ask(List<PromptMessage> history, PromptMessage next_msg) {
        history.add(next_msg);
        var answer = ask(history);
        history.add(answer);
        return answer;
    }
}
