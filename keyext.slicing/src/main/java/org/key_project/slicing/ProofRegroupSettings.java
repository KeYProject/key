/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

public class ProofRegroupSettings extends AbstractPropertiesSettings {
    private static final String PREFIX = "[ProofRegrouping]Group";
    private static final List<String> DEFAULT_GROUPS = List.of("Propositional expansion",
        "Negation/conjunctive normal form", "Polynomial/inequation normal form", "Simplification");

    private final List<PropertyEntry<String>> groups = new ArrayList<>();

    @Override
    public void readSettings(Properties props) {
        for (var key : props.keySet()) {
            var k = (String) key;
            var v = props.get(k);
            if (k.startsWith(PREFIX)) {
                var groupName = k.substring(PREFIX.length());
                var prop = createStringProperty(PREFIX + groupName, "");
                prop.set((String) v);
                groups.add(prop);
            }
        }
        if (groups.isEmpty()) {
            addGroup(DEFAULT_GROUPS.get(0), List.of("alpha", "delta"));
            addGroup(DEFAULT_GROUPS.get(1),
                List.of("negationNormalForm", "conjNormalForm"));
            addGroup(DEFAULT_GROUPS.get(2),
                List.of("polySimp_expand", "polySimp_normalise", "polySimp_newSym",
                    "polySimp_pullOutGcd", "polySimp_applyEq", "polySimp_applyEqRigid",
                    "polySimp_directEquations", "polySimp_applyEqPseudo",
                    "inEqSimp_forNormalisation", "inEqSimp_directInEquations",
                    "inEqSimp_propagation",
                    "inEqSimp_nonLin", "inEqSimp_signCases",
                    "inEqSimp_expand", "inEqSimp_saturate",
                    "inEqSimp_pullOutGcd", "inEqSimp_special_nonLin",
                    "simplify_literals"));
            addGroup(DEFAULT_GROUPS.get(3),
                List.of("simplify", "simplify_select", "simplify_enlarging"));
        }
    }

    public void addGroup(String name, List<String> ruleSets) {
        groups.add(createStringProperty(PREFIX + name, String.join(",", ruleSets)));
    }

    public void updateGroup(String name, List<String> ruleSets) {
        for (var prop : groups) {
            if (prop.getKey().equals(PREFIX + name)) {
                prop.set(String.join(",", ruleSets));
            }
        }
    }

    public Map<String, List<String>> getGroups() {
        Map<String, List<String>> m = new HashMap<>();
        for (var pe : groups) {
            var name = pe.getKey().substring(PREFIX.length());
            m.put(name, List.of(pe.get().split(",")));
        }
        return m;
    }

    public Map<String, List<String>> getUserGroups() {
        Map<String, List<String>> m = new HashMap<>();
        for (var pe : groups) {
            var name = pe.getKey().substring(PREFIX.length());
            if (DEFAULT_GROUPS.contains(name)) {
                continue;
            }
            m.put(name, List.of(pe.get().split(",")));
        }
        return m;
    }

    public void removeGroup(String name) {
        PropertyEntry<String> toRemove = null;
        for (var pe : groups) {
            if (pe.getKey().substring(PREFIX.length()).equals(name)) {
                toRemove = pe;
                break;
            }
        }
        groups.remove(toRemove);
        propertyEntries.remove(toRemove);
        properties.remove(toRemove);
    }
}
