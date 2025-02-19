/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.adapters;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Type;

import de.uka.ilkd.key.macros.ProofMacro;

import org.key_project.logic.op.Function;

import com.google.gson.*;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonToken;
import com.google.gson.stream.JsonWriter;
import org.keyproject.key.api.data.MacroDescription;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.23)
 */
public class KeyAdapter {
    // private final BiMap<String, WeakReference<Object>> map = HashBiMap.create(1024);
    // private final TypeAdapter<Object> adaptor;

    public KeyAdapter(GsonBuilder gson) {
        gson.registerTypeAdapter(File.class, new FileTypeAdapter());
        // gson.registerTypeAdapter(Function.class, new FunctionSerializer());
        // gson.registerTypeAdapter(ProofMacro.class, new MacroSerializer());
    }


    /*
     * //translating entities to identification strings
     * public void insert(Identifiable p) {
     * var id = p.identification();
     * if (!map.containsKey(id)) {
     * map.put(id, new WeakReference<>(p));
     * }
     * }
     *
     * public Object find(String id) {
     * return map.get(id).get();
     * }
     * //endregion
     */

    static class MacroSerializer implements JsonSerializer<ProofMacro> {
        @Override
        public JsonElement serialize(ProofMacro src, Type typeOfSrc,
                JsonSerializationContext context) {
            return context.serialize(MacroDescription.from(src));
        }
    }

    public static class FileTypeAdapter extends TypeAdapter<File> {
        @Override
        public void write(JsonWriter out, File value) throws IOException {
            out.value(String.valueOf(value));
        }

        @Override
        public File read(JsonReader in) throws IOException {
            var tokenType = in.peek();
            if (tokenType == JsonToken.NULL) {
                in.nextNull();
                return null;
            }
            return new File(in.nextString());
        }
    }

    static class FunctionSerializer implements JsonSerializer<Function> {
        @Override
        public JsonElement serialize(Function src, Type typeOfSrc,
                JsonSerializationContext context) {
            var obj = new JsonObject();
            obj.add("name", context.serialize(src.name().toString()));
            obj.add("skolemConstant", context.serialize(src.isSkolemConstant()));
            obj.add("isRigid", context.serialize(src.isRigid()));
            obj.add("isUnique", context.serialize(src.isUnique()));
            obj.add("sort", context.serialize(src.sort()));
            obj.add("argSorts", context.serialize(src.argSorts()));
            return obj;
        }
    }

    public static class ThrowableAdapter implements JsonSerializer<Throwable> {
        @Override
        public JsonElement serialize(Throwable src, Type typeOfSrc,
                JsonSerializationContext context) {
            var obj = new JsonObject();
            obj.add("$class", context.serialize(src.getClass().getSimpleName()));
            obj.add("message", context.serialize(src.getMessage()));
            obj.add("cause", context.serialize(src.getCause()));
            return obj;
        }
    }

    /*
     * class IdentifiableTypeAdapter implements JsonSerializer<Identifiable>,
     * JsonDeserializer<Identifiable> {
     *
     * @Override
     * public Identifiable deserialize(JsonElement json, Type typeOfT, JsonDeserializationContext
     * context) throws JsonParseException {
     * return (Identifiable) find(json.getAsString());
     * }
     *
     * @Override
     * public JsonElement serialize(Identifiable src, Type typeOfSrc, JsonSerializationContext
     * context) {
     * insert(src);
     * return context.serialize(src.identification());
     * }
     * }
     */
}
