package org.key_project.rusty.parser.hir.item;

import com.google.gson.JsonDeserializationContext;
import com.google.gson.JsonDeserializer;
import com.google.gson.JsonElement;
import com.google.gson.JsonParseException;
import org.key_project.rusty.parser.hir.Span;
import org.key_project.rusty.parser.hir.hirty.HirTy;

import java.lang.reflect.Type;

public interface FnRetTy {
    record Return(HirTy ty) implements FnRetTy {
    }

    record DefaultReturn(Span span) implements FnRetTy {}

    class Adapter implements JsonDeserializer<FnRetTy> {
        @Override
        public FnRetTy deserialize(JsonElement jsonElement, Type type, JsonDeserializationContext jsonDeserializationContext) throws JsonParseException {
            var obj = jsonElement.getAsJsonObject();
            if (obj.has("Return")) {
                return new Return(jsonDeserializationContext.deserialize(obj.get("Return"), HirTy.class));
            }
            return new DefaultReturn(jsonDeserializationContext.deserialize(obj.get("DefaultReturn"), Span.class));
        }
    }
}
