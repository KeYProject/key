package org.key_project.key.llm;

import com.google.gson.GsonBuilder;
import org.apache.hc.client5.http.classic.methods.HttpPost;
import org.apache.hc.client5.http.impl.classic.AbstractHttpClientResponseHandler;
import org.apache.hc.client5.http.impl.classic.HttpClients;
import org.apache.hc.core5.http.HttpEntity;
import org.apache.hc.core5.http.ParseException;
import org.apache.hc.core5.http.io.entity.EntityUtils;
import org.apache.hc.core5.http.io.entity.StringEntity;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Map;
import java.util.concurrent.Callable;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
public class LlmClient implements Callable<Map<String, Object>> {
    private final LlmSession llmSession;
    private final LlmContext context;
    private final LlmContext.LlmMessage prompt;

    public LlmClient(LlmSession llmSession, LlmContext context, String message) {
        this.llmSession = llmSession;
        this.context = context;
        this.prompt = new LlmContext.LlmMessage("user", message);
    }

    @Override
    public Map<String, Object> call() throws Exception {
        var url = llmSession.getApiEndpoint() + "/chat/completions";
        var request = new HttpPost(url);

        request.addHeader("Authorization", "Bearer " + llmSession.getAuthToken());
        request.addHeader("Content-Type", "application/json");
        request.addHeader("Accept", "application/json");

        var msg = new ArrayList<>(context.getMessages());
        msg.add(prompt);

        var data = Map.of(
                "model", llmSession.getModel(),
                "messages", msg);

        var gson = new GsonBuilder().create();
        var stringBody = gson.toJson(data);
        request.setEntity(new StringEntity(stringBody));

        try (var client = HttpClients.createDefault()) {
            return client.execute(request, new GsonHttpClientResponseHandler());
        }
    }


    private static class GsonHttpClientResponseHandler extends AbstractHttpClientResponseHandler<Map<String, Object>> {
        @Override
        public Map<String, Object> handleEntity(HttpEntity entity) throws IOException {
            String content = null;
            try {
                content = EntityUtils.toString(entity);
            } catch (ParseException e) {
                throw new RuntimeException(e);
            }
            //LoggerFactory.getLogger(LlmClient.class).error("Could not parse json response {}",content);
            try {
                return new GsonBuilder().create().fromJson(content, Map.class);
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }
    }
}
