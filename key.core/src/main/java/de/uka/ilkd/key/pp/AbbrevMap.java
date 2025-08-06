/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.JTerm;

import org.key_project.util.collection.Pair;

public class AbbrevMap {

    /**
     * HashMaps used to store the mappings from Term to String, String to Term and Term to Enabled.
     */
    private final HashMap<AbbrevWrapper, String> termstring;
    private final HashMap<String, AbbrevWrapper> stringterm;

    /**
     * Enabled is set true if a abbreviation should be used when printing the term.
     */
    private final HashMap<AbbrevWrapper, Boolean> termenabled;

    /**
     * Creates a AbbrevMap.
     */
    public AbbrevMap() {
        termstring = new LinkedHashMap<>();
        stringterm = new LinkedHashMap<>();
        termenabled = new LinkedHashMap<>();
    }

    /**
     * Associates a Term and its abbreviation in this map.
     *
     * @param t a term
     * @param abbreviation the abbreviation for of this term
     * @param enabled true if the abbreviation should be used (e.g. when printing the term), false
     *        otherwise.
     */
    public void put(JTerm t, String abbreviation, boolean enabled) throws AbbrevException {
        AbbrevWrapper scw;
        if (containsTerm(t)) {
            throw new AbbrevException("A abbreviation for " + t + " already exists", true);
        }
        if (containsAbbreviation(abbreviation)) {
            throw new AbbrevException("The abbreviation " + abbreviation + " is already"
                + " in use for: " + getTerm(abbreviation), false);
        }
        scw = new AbbrevWrapper(t);
        termstring.put(scw, abbreviation);
        stringterm.put(abbreviation, scw);
        termenabled.put(scw, enabled ? Boolean.TRUE : Boolean.FALSE);
    }

    /**
     * Changes the abbreviation of t to abbreviation. If the AbbrevMap doesn't contain t nothing
     * happens.
     *
     * @throws AbbrevException if the abbreviation is already in use.
     */
    public void changeAbbrev(JTerm t, String abbreviation) throws AbbrevException {
        if (containsTerm(t)) {
            AbbrevWrapper scw;
            if (containsAbbreviation(abbreviation)) {
                throw new AbbrevException("The abbreviation " + abbreviation + " is already"
                    + " in use for: " + getTerm(abbreviation), false);
            }
            scw = new AbbrevWrapper(t);
            stringterm.remove(termstring.get(scw));
            termstring.put(scw, abbreviation);
            stringterm.put(abbreviation, scw);
        }
    }

    /**
     * Changes the abbreviation <code>abbreviation</code> to <code>t</code>. If the AbbrevMap
     * doesn't contain <code>abbreviation</code> nothing happens.
     *
     * @throws AbbrevException If an abbreviation for t already exists.
     */
    public void changeAbbrev(String abbreviation, JTerm t, boolean enabled) throws AbbrevException {
        if (containsAbbreviation(abbreviation)) {
            AbbrevWrapper scw;
            if (containsTerm(t)) {
                throw new AbbrevException("A abbreviation for " + t + " already exists", true);
            }
            scw = new AbbrevWrapper(t);
            stringterm.remove(termstring.get(scw));
            termstring.put(scw, abbreviation);
            stringterm.put(abbreviation, scw);
            termenabled.put(scw, enabled ? Boolean.TRUE : Boolean.FALSE);
        }
    }

    /**
     * Returns true if the map contains the abbreviation s.
     */
    public boolean containsAbbreviation(String s) {
        return stringterm.containsKey(s);
    }

    /**
     * Returns true if the map contains the term t.
     */
    public boolean containsTerm(JTerm t) {
        return termstring.containsKey(new AbbrevWrapper(t));
    }

    /**
     * Returns the term which is mapped to the abbreviation s, null if no term is mapped to the
     * abbreviation.
     */
    public JTerm getTerm(String s) {
        var term = stringterm.get(s);
        return term == null ? null : term.getTerm();
    }

    /**
     * Returns the abbreviation mapped to the term t. Returns null if no abbreviation is mapped to
     * t.
     */
    public String getAbbrev(JTerm t) {
        return "@" + termstring.get(new AbbrevWrapper(t));
    }

    /**
     * Returns true if the mapping is enabled, which means that the abbreviation may be used.
     */
    public boolean isEnabled(JTerm t) {
        Boolean b = termenabled.get(new AbbrevWrapper(t));
        if (b != null) {
            return b;
        }
        return false;
    }

    /**
     * Sets the mapping of the term t to its abbreviation enabled or disabled
     *
     * @param t a Term
     * @param enabled true if the abbreviation of t may be used.
     */
    public void setEnabled(JTerm t, boolean enabled) {
        termenabled.put(new AbbrevWrapper(t), enabled ? Boolean.TRUE : Boolean.FALSE);
    }

    /**
     * Exports the current abbreviation map as a sequence of pairs of the term and its abbreviation.
     * Note, this will allocate a new data structure each time.
     */
    public Collection<Pair<JTerm, String>> export() {
        return termstring.entrySet().stream().map(e -> new Pair<>(e.getKey().t, e.getValue()))
                .collect(Collectors.toList());

    }

    public void remove(JTerm prevTerm) {
        setEnabled(prevTerm, false);
    }

    public record AbbrevWrapper(JTerm t) {

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof AbbrevWrapper scw)) {
                return false;
            }
            if (scw.getTerm() == t) {
                return true;
            }
            return t.equals(scw.getTerm());
        }

        public JTerm getTerm() {
            return t;
        }
    }
}
