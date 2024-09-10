package org.key_project.llmsynth.oracles;

import org.key_project.llmsynth.prompts.PromptMessage;

import java.util.List;

/**
 * A streamlined interface to talk to oracles of any kind
 */
public interface OracleEndpoint {
    /**
     *
     * @param prompts A history of the conversation
     * @return The ansswer of the oracle
     */
    PromptMessage ask(List<PromptMessage> prompts);

    /**
     * Will add next_msg to the history list
     * @param history A history of the conversation
     * @param next_msg The prompt to ask
     * @return The answer of the oracle
     */
    default PromptMessage ask(List<PromptMessage> history, PromptMessage next_msg) {
        history.add(next_msg);
        var answer = ask(history);
        history.add(answer);
        return answer;
    }
}
