/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api;

import java.lang.reflect.Type;

import com.google.gson.*;

/**
 * <a href=
 * "https://stackoverflow.com/questions/39999278/gson-how-to-include-class-name-property-when-serializing-object-of-any-type">Stackoverflow
 * post</a>
 */
public class GenericSerializer implements JsonSerializer<Object> /* , JsonDeserializer<Object> */ {

    private static final String CLASS_PROPERTY_NAME = "$class";
    private final Gson gson;

    public GenericSerializer() {
        gson = new Gson();
    }

    public GenericSerializer(Gson gson) {
        this.gson = gson;
    }

    /*
     * @Override
     * public Object deserialize(JsonElement json, Type typeOfT,
     * JsonDeserializationContext context) throws JsonParseException {
     *
     * Class<?> actualClass;
     * if (json.isJsonObject()) {
     * JsonObject jsonObject = json.getAsJsonObject();
     * String className = jsonObject.get(CLASS_PROPERTY_NAME).getAsString();
     * try {
     * actualClass = Class.forName(className);
     * } catch (ClassNotFoundException e) {
     * e.printStackTrace();
     * throw new JsonParseException(e.getMessage());
     * }
     * } else {
     * actualClass = typeOfT.getClass();
     * }
     *
     * return gson.fromJson(json, actualClass);
     * }
     */

    @Override
    public JsonElement serialize(Object src, Type typeOfSrc,
            JsonSerializationContext context) {
        JsonElement retValue = gson.toJsonTree(src);
        if (retValue.isJsonObject()) {
            retValue.getAsJsonObject().addProperty(CLASS_PROPERTY_NAME,
                src.getClass().getSimpleName());
        }
        return retValue;
    }

}
