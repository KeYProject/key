/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import java.io.File;
import java.lang.reflect.Type;
import java.nio.file.Path;
import java.nio.file.Paths;

import com.google.gson.*;
import org.jspecify.annotations.Nullable;

/**
 * Value class of a uniform resource identifier
 *
 * @author Alexander Weigl
 * @version 1 (11/30/25)
 */
public record Uri(String uri) {
    public static @Nullable Uri from(File sel) {
        return new Uri(sel.toURI().toString());
    }

    public Path asPath() {
        if (uri.startsWith("file://")) {
            return Paths.get(uri.substring("file://".length()));
        }

        try {
            return Paths.get(uri);
        } catch (Exception ignored) {
            throw new RuntimeException("Illegal file URI");
        }
    }

    public static class UriSerializer implements JsonSerializer<Uri>, JsonDeserializer<Uri> {
        @Override
        public Uri deserialize(JsonElement jsonElement, Type type,
                JsonDeserializationContext jsonDeserializationContext) throws JsonParseException {
            return new Uri(jsonElement.getAsString());
        }

        @Override
        public JsonElement serialize(Uri uri, Type type,
                JsonSerializationContext jsonSerializationContext) {
            return jsonSerializationContext.serialize(uri);
        }
    }
}
