/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;
import de.uka.ilkd.key.settings.Configuration;

public class ProofRegroupSettings extends AbstractPropertiesSettings {
    private static final String CATEGORY = "ProofRegrouping";
    private static final List<String> DEFAULT_GROUPS = List.of("Propositional expansion",
        "Negation/conjunctive normal form", "Polynomial/inequation normal form", "Simplification");

    private final List<PropertyEntry<String>> groups = new ArrayList<>();

    public ProofRegroupSettings() {
        super(CATEGORY);
    }

    @Override
    public void readSettings(Configuration configuration) {
        var cat = configuration.getSection(category);
        if (cat != null) {
            for (var entry : cat.getEntries()) {
                var groupName = entry.getKey();
                var v = entry.getValue();
                var prop = createStringProperty(groupName, "");
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
        groups.add(createStringProperty(name, String.join(",", ruleSets)));
    }

    public void updateGroup(String name, List<String> ruleSets) {
        for (var prop : groups) {
            if (prop.getKey().equals(name)) {
                prop.set(String.join(",", ruleSets));
            }
        }
    }

    public Map<String, List<String>> getGroups() {
        Map<String, List<String>> m = new HashMap<>();
        for (var pe : groups) {
            var name = pe.getKey();
            m.put(name, List.of(pe.get().split(",")));
        }
        return m;
    }

    public Map<String, List<String>> getUserGroups() {
        Map<String, List<String>> m = new HashMap<>();
        for (var pe : groups) {
            var name = pe.getKey();
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
            if (pe.getKey().equals(name)) {
                toRemove = pe;
                break;
            }
        }
        groups.remove(toRemove);
        propertyEntries.remove(toRemove);
    }
}
