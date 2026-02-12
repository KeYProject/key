/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Map;
import java.util.TreeMap;

import org.key_project.logic.HasMeta;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/// MetaSpace is a namespace for storing additional information
///
/// @author weigl
@NullMarked
public class MetaSpace {
    public static final String SPACE_PREFIX_DOC = "doc/";
    public static final String SPACE_PREFIX_ORIGIN = "origin/";

    private @Nullable MetaSpace parent;
    private final Map<String, Object> metadata = new TreeMap<>();

    public MetaSpace() {
    }

    public MetaSpace(Map<String, Object> documentation) {
        this.metadata.putAll(documentation);
    }

    public MetaSpace(MetaSpace parent) {
        this.parent = parent;
    }

    private @Nullable Object findMetadata(String key) {
        return metadata.get(key);
    }

    public @Nullable String findDocumentation(HasMeta entity) {
        if (entity.getDocumentation() != null) {
            return entity.getDocumentation();
        }
        return (String) findMetadata(SPACE_PREFIX_DOC + entity.getMetaKey());
    }

    /**
     * Returns a human-readable source of this term. For example the filename with line and offset.
     */
    public @Nullable String findOrigin(HasMeta entity) {
        return (String) findMetadata(SPACE_PREFIX_ORIGIN + entity.getMetaKey());
    }

    public void add(MetaSpace space) {
        this.metadata.putAll(space.metadata);
    }

    public @Nullable MetaSpace parent() {
        return parent;
    }

    public void setDocumentation(HasMeta entity, @Nullable String doc) {
        if (doc != null && doc.isBlank()) {
            return;
        }
        setMetadata(SPACE_PREFIX_DOC, entity, doc);
    }

    public void setOrigin(HasMeta entity, @Nullable String origin) {
        if (origin != null && origin.isBlank()) {
            return;
        }
        setMetadata(SPACE_PREFIX_ORIGIN, entity, origin);
    }

    private void setMetadata(String prefix, HasMeta entity, @Nullable Object val) {
        var key = prefix + entity.getMetaKey();
        if (val == null) {
            metadata.remove(key);
        } else {
            metadata.put(key, val);
        }
    }


    public MetaSpace copy() {
        return new MetaSpace(metadata);
    }
}
