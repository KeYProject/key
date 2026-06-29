/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import java.util.Map;
import java.util.TreeMap;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/// MetaSpace is a namespace for storing additional information (metadata) for logic entities.
/// It serves (currently) as a centralized repository for documentation and origin information.
/// **Thread Safety Warning:** MetaSpace is **not thread-safe**. It is filled during parsing and
/// should be
/// considered read-only during normal operation. If you need to modify a MetaSpace in parallel
/// code, you must
/// implement your own synchronization mechanisms.
///
/// @author weigl
/// @see HasMetaSpaceKey
@NullMarked
public class MetaSpace {
    /// Prefix for documentation metadata keys.
    public static final String SPACE_PREFIX_DOC = "doc/";
    /// Prefix for origin/source location metadata keys.
    public static final String SPACE_PREFIX_ORIGIN = "origin/";

    /// Reference to a parent MetaSpace for hierarchical lookups.
    private @Nullable MetaSpace parent;
    /// Internal storage for metadata (TreeMap implementation).
    private final Map<String, Object> metadata = new TreeMap<>();

    /// Creates an empty MetaSpace instance with no parent and no metadata.
    public MetaSpace() {
    }

    /// Creates a MetaSpace initialized with the provided documentation map.
    ///
    /// @param documentation A map of string keys to object values to initialize the metadata
    public MetaSpace(Map<String, Object> documentation) {
        this.metadata.putAll(documentation);
    }

    /// Creates a MetaSpace with a reference to a parent MetaSpace.
    ///
    /// @param parent The parent MetaSpace for hierarchical metadata lookup
    public MetaSpace(MetaSpace parent) {
        this.parent = parent;
    }

    private @Nullable Object findMetadata(String key) {
        if (metadata.containsKey(key)) {
            return metadata.get(key);
        }
        if (parent != null) {
            return parent.findMetadata(key);
        }
        return null;
    }

    /// Retrieves the documentation associated with a logic entity.
    ///
    /// First checks if the entity itself has direct documentation via `entity.getDocumentation()`.
    /// If not found, looks up metadata using the key `"doc/" + entity.getMetaKey()`.
    ///
    /// @param entity An entity implementing [HasMetaSpaceKey]
    /// @return The documentation string if found, or `null` if no documentation exists
    public @Nullable String findDocumentation(HasMetaSpaceKey entity) {
        if (entity.getDocumentation() != null) {
            return entity.getDocumentation();
        }
        return (String) findMetadata(SPACE_PREFIX_DOC + entity.getMetaKey());
    }

    /// Returns a human-readable source location for a logic entity.
    /// For example, the filename with line and offset (e.g., "MyFile.key:42:15").
    ///
    /// @param entity An entity implementing [HasMetaSpaceKey]
    /// @return The origin string if found, or `null` if no origin information exists
    public @Nullable String findOrigin(HasMetaSpaceKey entity) {
        return (String) findMetadata(SPACE_PREFIX_ORIGIN + entity.getMetaKey());
    }

    /// Merges another MetaSpace into this one.
    ///
    /// All metadata from the provided space is copied into this space.
    /// Existing keys may be overwritten.
    ///
    /// @param space The MetaSpace whose metadata should be added to this instance
    public void add(MetaSpace space) {
        this.metadata.putAll(space.metadata);
    }

    /// Returns the parent MetaSpace if one exists.
    ///
    /// @return The parent MetaSpace, or `null` if no parent is set
    public @Nullable MetaSpace parent() {
        return parent;
    }

    /// Sets the documentation for a logic entity.
    ///
    /// Blank strings are ignored (no operation performed).
    /// If `doc` is `null`, the metadata entry is removed.
    ///
    /// @param entity An entity implementing [HasMetaSpaceKey]
    /// @param doc The documentation string, or `null` to remove existing documentation
    public void setDocumentation(HasMetaSpaceKey entity, @Nullable String doc) {
        if (doc != null && doc.isBlank()) {
            return;
        }
        setMetadata(SPACE_PREFIX_DOC, entity, doc);
    }

    /// Sets the origin/source location for a logic entity.
    ///
    /// Blank strings are ignored (no operation performed).
    /// If `origin` is `null`, the metadata entry is removed.
    ///
    /// @param entity An entity implementing [HasMetaSpaceKey]
    /// @param origin The origin string, or `null` to remove existing origin info
    public void setOrigin(HasMetaSpaceKey entity, @Nullable String origin) {
        if (origin != null && origin.isBlank()) {
            return;
        }
        setMetadata(SPACE_PREFIX_ORIGIN, entity, origin);
    }

    /// Internal method to set metadata for a logic entity.
    ///
    /// @param prefix The prefix for the metadata key (e.g., "doc/" or "origin/")
    /// @param entity An entity implementing [HasMetaSpaceKey]
    /// @param val The value to store, or `null` to remove the metadata entry
    private void setMetadata(String prefix, HasMetaSpaceKey entity, @Nullable Object val) {
        var key = prefix + entity.getMetaKey();
        if (val == null) {
            metadata.remove(key);
        } else {
            metadata.put(key, val);
        }
    }


    /// Creates a shallow copy of this MetaSpace.
    ///
    /// @return A new MetaSpace instance containing the same metadata
    public MetaSpace copy() {
        return new MetaSpace(metadata);
    }
}
