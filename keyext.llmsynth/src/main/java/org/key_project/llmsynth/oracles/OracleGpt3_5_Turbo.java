package org.key_project.llmsynth.oracles;

import com.theokanning.openai.completion.chat.*;
import com.theokanning.openai.service.OpenAiService;
import io.reactivex.Flowable;
import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptAnswer;
import org.key_project.llmsynth.prompts.PromptReason;

import java.util.*;
import java.util.stream.Stream;

class MessageBuffer {
    public ChatMessage prompt;
    public ChatMessage answer;

    public MessageBuffer(ChatMessage prompt, ChatMessage answer) {
        this.prompt = prompt;
        this.answer = answer;
    }
}

public class OracleGpt3_5_Turbo {
    public static boolean print_Messages = false;
    OpenAiService service;

    private final String token;

    private final Map<Prompt, List<ChatMessage>> history = new HashMap<>();
    private final ChatMessage systemMessage = new ChatMessage(ChatMessageRole.SYSTEM.value(), "");

    public OracleGpt3_5_Turbo(String token) {
        service = new OpenAiService(token);
        this.token = token;
    }

    // Finalize
    public void shutdown() {
        service.shutdownExecutor();
    }

    public void resetConnection() {
        this.shutdown();
        this.service = new OpenAiService(this.token);
    }

    public PromptAnswer answerPrompt(PromptReason generatedFrom, Prompt prompt) {
        ChatMessage question = convert(prompt);
        ChatMessage answer = null;
        int requestCount = 0;
        do {
            try {
                final boolean[] previousWasStop = {true};
                // todo: hasNext isn't nececcarily correct
                List<ChatMessage> chats = Stream.iterate(generatedFrom, pr -> pr.getParent() != null, PromptReason::getParent)
                        .takeWhile(pr -> {
                            boolean sentinel = previousWasStop[0];
                            previousWasStop[0] = !pr.getPrompt().hasRemoveHistoryFlag();
                            return sentinel;
                        })
                        .map(PromptReason::getPrompt)
                        .map(history::get)
                        .collect(ArrayList::new, ArrayList::addAll, ArrayList::addAll);
                // todo: ^  the list can be buffered to save allocationss (maximum depth of the tree is known)

                // todo: the answers to the prompt may not be in the right order here
                chats.add(systemMessage);
                Collections.reverse(chats);
                chats.add(question);

                ChatCompletionRequest ccr = createCompletionRequest(chats);
                Flowable<ChatCompletionChunk> flowable = service.streamChatCompletion(ccr);
                answer = service
                        .mapStreamToAccumulator(flowable)
                        .lastElement()
                        .blockingGet()
                        .getAccumulatedMessage();
            } catch (RuntimeException e) {
                System.err.println("Error prompting GPT, resetting connection: " + e.getMessage());
                this.resetConnection();
            }
        } while (answer == null && requestCount++ < 3);

        history.put(prompt, List.of(answer, question));

        if (print_Messages) {
            System.out.println("=============================================================");
            System.out.println(prompt.toString());
            System.out.println("-------------------------------------------------------------");
            System.out.println(answer.getContent());
        }
        return new PromptAnswer(prompt, answer.getContent());
    }

    private ChatMessage convert(Prompt prompt) {
        var text = prompt.toString();
        return new ChatMessage(ChatMessageRole.USER.value(), text);
    }

    private ChatCompletionRequest createCompletionRequest(List<ChatMessage> messages) {
        return ChatCompletionRequest
                .builder()
                .model("gpt-3.5-turbo-0125")
                //.model("gpt-4o")
                .messages(messages)
                .n(1)
                .maxTokens(512)
                .logitBias(new HashMap<>())
                .build();
    }
}
