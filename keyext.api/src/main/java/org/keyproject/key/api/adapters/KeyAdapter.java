/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.adapters;

import java.io.File;
import java.io.IOException;
import java.lang.ref.WeakReference;
import java.lang.reflect.Type;

import de.uka.ilkd.key.Identifiable;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Proof;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.gson.*;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonWriter;
import org.keyproject.key.api.data.MacroDescription;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.23)
 */
public class KeyAdapter {
    private final BiMap<String, WeakReference<Object>> map = HashBiMap.create(1024);
    // private final TypeAdapter<Object> adaptor;

    public KeyAdapter(GsonBuilder gson) {
        gson.registerTypeAdapter(File.class, new FileTypeAdapter());
        gson.registerTypeAdapter(Function.class, new FunctionTypeAdapter());
        gson.registerTypeAdapter(Proof.class, new IdentifiableTypeAdapter());
        gson.registerTypeAdapter(ProofMacro.class, new MacroTypeAdapter());
        // adaptor = gson.create().getAdapter(Object.class);
    }


    // translating entities to identification strings
    public String insert(Identifiable p) {
        var id = p.identification();
        if (!map.containsKey(id)) {
            map.put(id, new WeakReference<>(p));
        }
        return id;
    }

    public Object find(String id) {
        return map.get(id).get();
    }
    // endregion

    class MacroTypeAdapter implements JsonSerializer<ProofMacro> {
        @Override
        public JsonElement serialize(ProofMacro src, Type typeOfSrc,
                JsonSerializationContext context) {
            return context.serialize(MacroDescription.from(src));
        }
    }

    class FileTypeAdapter extends TypeAdapter<File> {
        @Override
        public void write(JsonWriter out, File value) throws IOException {
            out.value(value.toString());
        }

        @Override
        public File read(JsonReader in) throws IOException {
            return new File(in.nextString());
        }
    }

    class FunctionTypeAdapter implements JsonSerializer<Function> {
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

    class IdentifiableTypeAdapter
            implements JsonSerializer<Identifiable>, JsonDeserializer<Identifiable> {
        @Override
        public Identifiable deserialize(JsonElement json, Type typeOfT,
                JsonDeserializationContext context) throws JsonParseException {
            return (Identifiable) find(json.getAsString());
        }

        @Override
        public JsonElement serialize(Identifiable src, Type typeOfSrc,
                JsonSerializationContext context) {
            insert(src);
            return context.serialize(src.identification());
        }
    }
}
