/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.java.ast;

import java.util.HashMap;
import java.util.Map;

/**
 *
 * @author Alexander Weigl
 * @version 1 (4/12/26)
 */
@SuppressWarnings("unchecked")
public class DefaultProperties implements Properties {
    private final Map<Property<?>, Object> properties = new HashMap<>();

    @Override
    public <T> T get(Property<T> property, T defaultValue) {
        return (T) properties.getOrDefault(property, defaultValue);
    }

    @Override
    public <T> T get(Property<T> property) {
        return (T) properties.get(property);
    }

    @Override
    public <T> boolean contains(Property<T> property) {
        return properties.containsKey(property);
    }

    @Override
    public <T> void set(Property<T> property, T value) {
        properties.put(property, value);
    }
}
