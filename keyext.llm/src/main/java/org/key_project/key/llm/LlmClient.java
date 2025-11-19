package org.key_project.key.llm;

import com.google.gson.GsonBuilder;
import org.apache.hc.client5.http.classic.methods.HttpGet;
import org.apache.hc.client5.http.classic.methods.HttpPost;
import org.apache.hc.client5.http.impl.classic.AbstractHttpClientResponseHandler;
import org.apache.hc.client5.http.impl.classic.HttpClients;
import org.apache.hc.core5.http.HttpEntity;
import org.apache.hc.core5.http.ParseException;
import org.apache.hc.core5.http.io.entity.EntityUtils;
import org.apache.hc.core5.http.io.entity.StringEntity;
import org.key_project.util.java.IOUtil;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Callable;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
public class LlmClient implements Callable<Map<String, Object>> {
    private final LlmSession llmSession;

    public LlmClient(LlmSession llmSession) {
        this.llmSession = llmSession;
    }

    @Override
    public Map<String, Object> call() throws Exception {
        var url = llmSession.getApiEndpoint() + "/chat/completions";
        var request = new HttpPost(url);

        request.addHeader("Authorization", "Bearer " + llmSession.getAuthToken());
        request.addHeader("Content-Type", "application/json");
        request.addHeader("Accept", "application/json");

        var data = Map.of(
                "model", "azure.gpt-4.1-mini",
                "messages", List.of(
                        createMessage("system", "Du bist ein hilfreicher Assistent am KIT."),
                        createMessage("user", "Erkläre das Prinzip der Rayleigh-Streuung indrei Sätzen.")
                )
        );
        var gson = new GsonBuilder().create();
        var stringBody = gson.toJson(data);
        request.setEntity(new StringEntity(stringBody));

        try (var client = HttpClients.createDefault()) {
            return client.execute(request, new GsonHttpClientResponseHandler());
        }
    }

    private Map<String, Object> createMessage(String role, String content) {
        return Map.of("role", role, "content", content);
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
