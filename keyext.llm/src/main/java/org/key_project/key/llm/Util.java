package org.key_project.key.llm;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;
import org.apache.hc.client5.http.classic.methods.HttpGet;
import org.apache.hc.client5.http.classic.methods.HttpPost;
import org.apache.hc.client5.http.impl.classic.HttpClients;
import org.apache.hc.core5.http.io.entity.StringEntity;

import java.io.IOException;
import java.util.Map;

/**
 *
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
public class Util {
    public static Object post(String url, String authToken, Map<String, Object> data) {
        var request = new HttpPost(url);
        request.addHeader("Authorization", "Bearer " + authToken);
        request.addHeader("Content-Type", "application/json");
        request.addHeader("Accept", "application/json");
        // Build request payload
        var gson = new GsonBuilder().create();
        var stringBody = gson.toJson(data);
        request.setEntity(new StringEntity(stringBody));

        try (var client = HttpClients.createDefault()) {
            return client.execute(request, new LlmClientExtended.GsonHttpClientResponseHandler());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public static JsonObject httpGet(String url, String authToken) {
        var request = new HttpGet(url);
        request.addHeader("Authorization", "Bearer " + authToken);
        request.addHeader("Content-Type", "application/json");
        request.addHeader("Accept", "application/json");
        try (var client = HttpClients.createDefault()) {
            return client.execute(request, new LlmClientExtended.GsonHttpClientResponseHandlerObj());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
