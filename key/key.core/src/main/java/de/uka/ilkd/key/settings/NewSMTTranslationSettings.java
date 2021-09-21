// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.settings;


import java.util.Collections;
import java.util.EventObject;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;

public class NewSMTTranslationSettings implements Settings, Cloneable {

    private static final String PREFIX = "[NewSMT]";
    private final Map<String, String> map = new HashMap<>();
    private final List<SettingsListener> listeners = new LinkedList<>();

    public NewSMTTranslationSettings() {
        // nothing to be done
    }

    public NewSMTTranslationSettings(NewSMTTranslationSettings toCopy) {
        map.putAll(toCopy.map);
    }

    @Override
    public NewSMTTranslationSettings clone() {
        return new NewSMTTranslationSettings(this);
    }

    @Override
    public void readSettings(Properties props) {
        for (Object k : props.keySet()) {
            String key = k.toString();
            if(key.startsWith(PREFIX)) {
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

    public Map<String, String> getMap() {
        return Collections.unmodifiableMap(map);
    }

    public String get(String key) {
        return map.get(key);
    }

    public String put(String key, String value) {
        String result = map.put(key, value);
        for (SettingsListener listener : listeners) {
            listener.settingsChanged(new EventObject(this));
        }
        return result;
    }

    @Override
    public void addSettingsListener(SettingsListener l) {
        listeners.add(l);
    }

    @Override
    public void removeSettingsListener(SettingsListener l) {
        listeners.remove(l);
    }

    public void copy(NewSMTTranslationSettings newTranslationSettings) {
        this.map.clear();
        this.map.putAll(newTranslationSettings.map);
    }
}