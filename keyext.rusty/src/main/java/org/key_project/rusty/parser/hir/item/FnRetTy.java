/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.item;

import java.lang.reflect.Type;

import org.key_project.rusty.parser.hir.Span;
import org.key_project.rusty.parser.hir.hirty.HirTy;

import com.google.gson.JsonDeserializationContext;
import com.google.gson.JsonDeserializer;
import com.google.gson.JsonElement;
import com.google.gson.JsonParseException;

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
