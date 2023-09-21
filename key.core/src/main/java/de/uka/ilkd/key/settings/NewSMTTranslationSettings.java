/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;


import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Properties;

/**
 * A collection of settings for the new (= 2021) SMT translation.
 *
 * Unlike the other settings, these settings do not have a fixed set of keys but are driven by
 * arbitrary keys.
 *
 * Hence, all that this class here does, is to essentially delegate methods to the underlying hash
 * map.
 *
 * The list of available settings can be retrieved from
 * {@link de.uka.ilkd.key.smt.newsmt2.SMTHandlerServices#getSMTProperties()}.
 *
 * @author Mattias Ulbrich
 */
public class NewSMTTranslationSettings extends AbstractSettings {
    private static final String PREFIX = "[NewSMT]";

    // Using a linked hash map to make the order deterministic in writing to
    // file
    private final Map<String, String> map = new LinkedHashMap<>();

    /**
     * Creates a new settings object in which no option is set.
     */
    public NewSMTTranslationSettings() {
        // nothing to be done
    }

    /**
     * Creates a new settings objects by copying the entries from the argument.
     *
     * @param toCopy a non-null settings object to take entries from
     */
    public NewSMTTranslationSettings(NewSMTTranslationSettings toCopy) {
        map.putAll(toCopy.map);
    }

    /**
     * Create a clone of this object. <code>s.clone()</code> is equivalent to
     *
     * <pre>
     *     new new NewSMTTranslationSettings(s);
     * </pre>
     *
     * @return
     */
    @Override
    public NewSMTTranslationSettings clone() {
        return new NewSMTTranslationSettings(this);
    }

    @Override
    public void readSettings(Properties props) {
        for (Object k : props.keySet()) {
            String key = k.toString();
            if (key.startsWith(PREFIX)) {
                map.put(key.substring(PREFIX.length()), props.getProperty(key));
            }
        }
    }

    @Override
    public void writeSettings(Properties props) {
        for (Entry<String, String> en : map.entrySet()) {
            props.put(PREFIX + en.getKey(), en.getValue());
        }
    }


    /**
     * Retreive an immutable view onto the underlying hash map
     *
     * @return a non-null immutable hashmap.
     */
    public Map<String, String> getMap() {
        return Collections.unmodifiableMap(map);
    }

    /**
     * Retrieve a single value from the underlying hashmap
     *
     * @param key the key to look up
     * @return the value for the key, null if not present
     */
    public String get(String key) {
        return map.get(key);
    }

    /**
     * Set a key-value-pair. All listeners are informed after the internal hashmap has been updated.
     *
     * @param key the non-null key to set
     * @param value the non-null value to set
     * @return the value that was in the map prior to the call (see {@link Map#put(Object, Object)}.
     */
    public String put(String key, String value) {
        var old = map.get(key);
        String result = map.put(Objects.requireNonNull(key), Objects.requireNonNull(value));
        firePropertyChange(key, old, value);
        return result;
    }

    public void copy(NewSMTTranslationSettings newTranslationSettings) {
        this.map.clear();
        this.map.putAll(newTranslationSettings.map);
    }
}
