/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir;

import java.lang.reflect.Type;

import com.google.gson.*;

public abstract class HirAdapter<T> implements JsonDeserializer<T> {
    private final String tagString;

    public HirAdapter() {
        tagString = "serde_tag";
    }

    @Override
    public T deserialize(JsonElement jsonElement, Type type,
            JsonDeserializationContext jsonDeserializationContext) throws JsonParseException {
        var obj = jsonElement.getAsJsonObject();
        try {
            var tag = obj.remove(this.tagString).getAsString();
            var clazz = getType(tag);
            if (clazz == null) {
                throw new JsonParseException(
                    "(" + getClass() + ") Unknown " + this.tagString + ": " + tag);
            }
            try {
                return jsonDeserializationContext.deserialize(obj, clazz);
            } catch (JsonSyntaxException e) {
                System.err.println(
                    "Error while deserializing " + getClass() + "::" + tag + ": " + e.getMessage());
                throw e;
            }
        } catch (RuntimeException e) {
            System.err.println("Error while deserializing " + getClass() + ": " + e.getMessage());
            throw e;
        }
    }

    public abstract Class<? extends T> getType(String tag);
}
