package org.key_project.rusty.parser.hir;

import com.google.gson.JsonDeserializationContext;
import com.google.gson.JsonDeserializer;
import com.google.gson.JsonElement;
import com.google.gson.JsonParseException;

import java.lang.reflect.Type;

public abstract class HirAdapter<T> implements JsonDeserializer<T> {
    @Override
    public T deserialize(JsonElement jsonElement, Type type, JsonDeserializationContext jsonDeserializationContext) throws JsonParseException {
        var obj = jsonElement.getAsJsonObject();
        var tag = obj.remove("serde_tag").getAsString();
        var clazz = getType(tag);
        if (clazz == null) {throw new JsonParseException("("+ getClass() + ") Unknown serde_tag: "+ tag);}
        return jsonDeserializationContext.deserialize(obj, clazz);
    }

    public abstract Class<? extends T> getType(String tag);
}
