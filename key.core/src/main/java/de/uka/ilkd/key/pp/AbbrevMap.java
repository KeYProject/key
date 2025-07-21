/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.JTerm;

import org.key_project.util.collection.Pair;

/**
 * This class realizes a 1:1 map for term abbreviations.
 * A term abbreviation is a label for a (complex) term structure that should be used for pretty
 * printing instead.
 * Abbreviations are also supported during parsing.
 * Use {@code @label} to access to a previous defined abbreviation
 * with label {@code label}.
 */
public class AbbrevMap {

    /**
     * HashMaps used to store the mappings from Term to String, String to Term and Term to enable.
     */
    private final Map<AbbrevWrapper, String> term2String = new LinkedHashMap<>();
    private final Map<String, AbbrevWrapper> string2Term = new LinkedHashMap<>();

    /**
     * Enabled is set true if an abbreviation should be used when printing the term.
     */
    private final Set<AbbrevWrapper> isTermEnabled = new HashSet<>();

    private final PropertyChangeSupport changeSupport = new PropertyChangeSupport(this);

    /**
     * Creates a AbbrevMap.
     */
    public AbbrevMap() {
    }

    /**
     * Associates a Term and its abbreviation in this map.
     *
     * @param t a term
     * @param abbreviation the abbreviation for of this term
     * @param enabled true if the abbreviation should be used (e.g., when printing the term), false
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
        forcePut(abbreviation, t);
    }

    /**
     * Changes the abbreviation of t to abbreviation.
     * If the AbbrevMap doesn't contain t, nothing happens.
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
            final var old = term2String.get(scw);
            string2Term.remove(old);
            term2String.put(scw, abbreviation);
            string2Term.put(abbreviation, scw);

            changeSupport.firePropertyChange(abbreviation, old, t);
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
            if (containsTerm(t)) {
                throw new AbbrevException("A abbreviation for " + t + " already exists", true);
            }
            var scw = new AbbrevWrapper(t);
            final var old = term2String.get(scw);
            string2Term.remove(old);
            term2String.put(scw, abbreviation);
            string2Term.put(abbreviation, scw);

            setEnabled(t, enabled);

            changeSupport.firePropertyChange(abbreviation, old, t);
        }
    }

    /**
     * Returns true if the map contains the abbreviation s.
     */
    public boolean containsAbbreviation(String s) {
        return string2Term.containsKey(s);
    }

    /**
     * Returns true if the map contains the term t.
     */
    public boolean containsTerm(JTerm t) {
        return term2String.containsKey(new AbbrevWrapper(t));
    }

    /**
     * Returns the term which is mapped to the abbreviation s, null if no term is mapped to the
     * abbreviation.
     */
    public JTerm getTerm(String s) {
        var term = string2Term.get(s);
        return term == null ? null : term.term();
    }

    /**
     * Returns the abbreviation mapped to the term t. Returns null if no abbreviation is mapped to
     * t.
     */
    public String getAbbrev(JTerm t) {
        return "@" + term2String.get(new AbbrevWrapper(t));
    }

    /**
     * Returns true if the mapping is enabled, which means that the abbreviation may be used.
     */
    public boolean isEnabled(JTerm t) {
        return isTermEnabled.contains(new AbbrevWrapper(t));
    }

    /**
     * Sets the mapping of the term t to its abbreviation enabled or disabled
     *
     * @param t a Term
     * @param enabled true if the abbreviation of t may be used.
     */
    public void setEnabled(JTerm t, boolean enabled) {
        var oldEnabled = isEnabled(t);
        var scw = new AbbrevWrapper(t);
        if (enabled)
            isTermEnabled.add(scw);
        else
            isTermEnabled.remove(scw);
        changeSupport.firePropertyChange("enabled", oldEnabled, enabled);
    }

    /**
     * Exports the current abbreviation map as a sequence of pairs of the terms and its
     * abbreviation.
     * Note, this will allocate a new data structure each time.
     */
    public Collection<Pair<JTerm, String>> export() {
        return term2String.entrySet().stream().map(e -> new Pair<>(e.getKey().term, e.getValue()))
                .collect(Collectors.toList());

    }

    public void remove(Term term) {
        var scw = new AbbrevWrapper(term);
        var s = term2String.get(scw);
        string2Term.remove(s);
        term2String.remove(scw);
        isTermEnabled.remove(scw);
        changeSupport.firePropertyChange(s, term, null);
    }

    /**
     * Sets the given abbreviation to term without checking of previous assignment.
     *
     * @param abbreviation the label of the abbreviation
     * @param t a term
     */
    public void forcePut(String abbreviation, Term t) {
        var scw = new AbbrevWrapper(t);
        term2String.put(scw, abbreviation);
        string2Term.put(abbreviation, scw);

        changeSupport.firePropertyChange(abbreviation, null, t);
        setEnabled(t, true);
    }

    public record AbbrevWrapper(Term term) {}

    public void addPropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.addPropertyChangeListener(listener);
    }

    public void removePropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.removePropertyChangeListener(listener);
    }
}
