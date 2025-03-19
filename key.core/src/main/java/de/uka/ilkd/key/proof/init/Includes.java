/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.io.File;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.io.RuleSource;


/**
 * Encapsulates 2 lists (one for LDT-include, one for "normal" includes) containing the filenames
 * parsed in the include-section of a <code>KeYFile</code>. <code>name2Source</code> maps the
 * entries of both lists to the corresponding RuleSources.
 */
public class Includes {

    /** a list containing the "normal" includes, represented as Strings */
    private final List<String> includes;
    /** a list containing the LDT includes, represented as Strings */
    private final List<String> ldtIncludes;
    /** contains mappings from filenames to RuleSources */
    private final HashMap<String, RuleSource> name2Source;
    private final List<File> files;

    public Includes() {
        includes = new LinkedList<>();
        ldtIncludes = new LinkedList<>();
        name2Source = new LinkedHashMap<>();
        files = new LinkedList<>();
    }

    private void put(String name, RuleSource source, List<String> list) {
        if (!list.contains(name)) {
            list.add(name);
            files.add(source.file());
            name2Source.put(name, source);
        }
    }

    /** adds a "normal" include. */
    public void put(String name, RuleSource source) {
        put(name, source, includes);
    }

    /** adds a LDT include. */
    public void putLDT(String name, RuleSource source) {
        put(name, source, ldtIncludes);
    }

    /**
     * returns the corresponding RuleSource to the filename <code>name</name>
     */
    public RuleSource get(String name) {
        return name2Source.get(name);
    }

    public List<File> getFiles() {
        return files;
    }

    /** removes the filename <code>name</code> and its mapping. */
    public void remove(String name) {
        includes.remove(name);
        ldtIncludes.remove(name);
        name2Source.remove(name);
    }

    /** return the list of non-LDT includes */
    public List<String> getIncludes() {
        return includes;
    }

    /** return the list of LDT includes */
    public List<String> getLDTIncludes() {
        return ldtIncludes;
    }

    public boolean isEmpty() {
        return name2Source.isEmpty();
    }


    public void putAll(Includes in) {
        includes.addAll(in.includes);
        ldtIncludes.addAll(in.ldtIncludes);
        name2Source.putAll(in.name2Source);
    }

    public Collection<RuleSource> getRuleSets() {
        return name2Source.values();
    }
}
