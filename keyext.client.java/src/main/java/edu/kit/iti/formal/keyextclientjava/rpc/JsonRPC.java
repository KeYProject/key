/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.keyextclientjava.rpc;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (24.11.24)
 */
public class JsonRPC {
    public static final String CONTENT_LENGTH = "Content-Length:";
    private static final Gson gson = new Gson();

    public static String createNotification(String method, Object... args) {
        return createRequest(null, method, args);
    }

    public static String createRequest(@Nullable String id, String method, Object... args) {
        JsonArray params = gson.toJsonTree(args).getAsJsonArray();
        return createRequest(id, method, params);
    }

    public static String createRequest(@Nullable String id, String method, JsonArray params) {
        var jsonObject = new JsonObject();
        jsonObject.addProperty("jsonrpc", "2.0");
        if (id != null) {
            jsonObject.addProperty("id", id);
        }

        jsonObject.addProperty("method", method);
        jsonObject.add("params", params);

        return jsonObject.toString();
    }

    public static String createResponse(String id, Object result) {
        return createResponse(id, gson.toJsonTree(result), null);
    }

    public static String createErrorReponse(String id, int code, String message,
            @Nullable Object data) {
        return createResponse(id, null, createError(code, message, data));
    }

    public static String createResponse(String id, @Nullable JsonElement result,
            @Nullable JsonObject error) {
        if (result != null && error != null) {
            throw new IllegalArgumentException("result and error at the same time is invalid");
        }

        if (!(result != null || error != null)) {
            throw new IllegalArgumentException("at least one of result and error must be not null");
        }

        var jsonObject = new JsonObject();
        jsonObject.addProperty("jsonrpc", "2.0");
        jsonObject.addProperty("id", id);

        if (result != null) {
            jsonObject.add("result", result);
        }
        if (error != null) {
            jsonObject.add("error", error);
        }

        return jsonObject.toString();
    }

    /**
     * 5.1 Error object
     * When a rpc call encounters an error, the Response Object MUST contain the error member with a
     * value that is a Object with the following members:
     * <p>
     * code
     * A Number that indicates the error type that occurred.
     * This MUST be an integer.
     * message
     * A String providing a short description of the error.
     * The message SHOULD be limited to a concise single sentence.
     * data
     * A Primitive or Structured value that contains additional information about the error.
     * This may be omitted.
     * The value of this member is defined by the Server (e.g. detailed error information, nested
     * errors etc.).
     *
     * @return
     */
    public static JsonObject createError(int code, String message, @Nullable Object data) {
        var jsonObject = new JsonObject();
        jsonObject.addProperty("code", code);
        jsonObject.addProperty("message", message);
        if (data != null) {
            jsonObject.add("data", gson.toJsonTree(data));
        }
        return jsonObject;
    }

    public static String addHeader(String response) {
        return "%s %d\r\n\r\n%s\r\n".formatted(CONTENT_LENGTH, response.length(), response);
    }
}
