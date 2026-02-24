/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Map;
import java.util.TreeMap;

import org.key_project.logic.HasDocumentation;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class DocSpace {
    private @Nullable DocSpace parent;
    private final Map<String, String> documentation = new TreeMap<>();

    public DocSpace() {}

    public DocSpace(Map<String, String> documentation) {
        this.documentation.putAll(documentation);
    }

    public DocSpace(DocSpace parent) {
        this.parent = parent;
    }

    public DocSpace(@Nullable DocSpace parent, Map<String, String> documentation) {
        this(documentation);
        this.parent = parent;
    }

    public @Nullable String find(String key) {
        var value = documentation.get(key);
        if (value != null)
            return value;
        if (parent != null)
            return parent.find(key);
        return null;
    }

    public @Nullable String find(HasDocumentation entity) {
        var doc = entity.getDocumentation();
        if (doc != null) {
            return doc;
        }
        return find(entity.getDocumentationKey());
    }

    public void add(DocSpace space) {
        this.documentation.putAll(space.documentation);
    }

    public @Nullable DocSpace parent() {
        return parent;
    }

    public void describe(HasDocumentation entity, @Nullable String doc) {
        if (doc == null) {
            return;
        }
        documentation.put(entity.getDocumentationKey(), doc);
    }

    public DocSpace copy() {
        return new DocSpace(parent, documentation);
    }
}
