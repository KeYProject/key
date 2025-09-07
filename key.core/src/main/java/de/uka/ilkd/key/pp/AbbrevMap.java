/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.*;

import de.uka.ilkd.key.logic.JTerm;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/// This class realizes a 1:1 map for term abbreviations.
/// A term abbreviation is a label for a (complex) term structure that should be used for pretty
/// printing instead.
/// Abbreviations are also supported during parsing.
/// Use `@label` to access to a previous defined abbreviation with label `label`.
@NullMarked
public class AbbrevMap {

    /// HashMaps used to store the mappings from Term to String, String to Term and Term to enable.
    private final Map<JTerm, String> term2String = new HashMap<>();
    private final Map<String, JTerm> string2Term = new HashMap<>();

    /// Enabled is set true if an abbreviation should be used when printing the term.
    private final Set<JTerm> isTermEnabled = new HashSet<>();

    private final PropertyChangeSupport changeSupport = new PropertyChangeSupport(this);

    /// Creates a AbbrevMap.
    public AbbrevMap() {
    }

    /// Associates a Term and its abbreviation in this map.
    ///
    /// @param t a term
    /// @param abbreviation the abbreviation for of this term
    /// @param enabled true if the abbreviation should be used (e.g., when printing the term), false
    /// otherwise.
    public void put(JTerm t, String abbreviation, boolean enabled) throws AbbrevException {
        if (containsTerm(t)) {
            throw new AbbrevException("An abbreviation for " + t + " already exists", true);
        }

        if (containsAbbreviation(abbreviation)) {
            throw new AbbrevException("The abbreviation " + abbreviation + " is already"
                + " in use for: " + getTerm(abbreviation), false);
        }
        forcePut(abbreviation, t);
        setEnabled(t, enabled);
    }

    /// Changes the abbreviation of t to abbreviation.
    /// If the AbbrevMap doesn't contain t, nothing happens.
    ///
    /// @throws AbbrevException when the abbreviation is already in use.
    public void changeAbbrev(JTerm t, String abbreviation) throws AbbrevException {
        if (containsTerm(t)) {
            if (containsAbbreviation(abbreviation)) {
                throw new AbbrevException("The abbreviation " + abbreviation + " is already"
                    + " in use for: " + getTerm(abbreviation), false);
            }

            final var old = term2String.get(t);
            string2Term.remove(old);
            term2String.put(t, abbreviation);
            string2Term.put(abbreviation, t);

            changeSupport.firePropertyChange(abbreviation, old, t);
        }
    }

    /// Changes the abbreviation `abbreviation` to `t`. If the [AbbrevMap]
    /// doesn't contain `abbreviation` nothing happens.
    ///
    /// @throws AbbrevException when an abbreviation for `t` already exists.
    public void changeAbbrev(String abbreviation, JTerm t, boolean enabled) throws AbbrevException {
        if (containsAbbreviation(abbreviation)) {
            if (containsTerm(t)) {
                throw new AbbrevException("A abbreviation for " + t + " already exists", true);
            }
            final var old = term2String.get(t);
            string2Term.remove(old);
            term2String.put(t, abbreviation);
            string2Term.put(abbreviation, t);

            setEnabled(t, enabled);

            changeSupport.firePropertyChange(abbreviation, old, t);
        }
    }

    /// Returns true if the map contains the abbreviation s.
    public boolean containsAbbreviation(String s) {
        return string2Term.containsKey(s);
    }

    /// Returns true if the map contains the term t.
    public boolean containsTerm(JTerm t) {
        return term2String.containsKey(t);
    }

    /// Returns the term which is mapped to the abbreviation s, null if no term is mapped to the
    /// abbreviation.
    public @Nullable JTerm getTerm(String s) {
        return string2Term.get(s);
    }

    /// Returns the abbreviation mapped to the term `t`.
    ///
    /// @return null if no abbreviation is mapped to t.
    public @Nullable String getAbbrev(JTerm t) {
        if (containsTerm(t)) {
            return "@" + term2String.get(t);
        }
        return null;
    }

    /// Returns true if the mapping is enabled, which means that the abbreviation may be used.
    public boolean isEnabled(JTerm t) {
        return isTermEnabled.contains(t);
    }

    /// Sets the mapping of the term t to its abbreviation enabled or disabled.
    ///
    /// @param t a [JTerm]
    /// @param enabled true if the abbreviation of `t` may be used.
    public void setEnabled(JTerm t, boolean enabled) {
        var oldEnabled = isEnabled(t);
        if (enabled) {
            isTermEnabled.add(t);
        } else {
            isTermEnabled.remove(t);
        }
        changeSupport.firePropertyChange("enabled", oldEnabled, enabled);
    }

    /// Exports the current abbreviation map as an entry set.
    public Set<Map.Entry<JTerm, String>> export() {
        return term2String.entrySet();

    }

    /// Removes the given `term` and its abbreviation completely from the underlying
    /// data structures.
    public void remove(JTerm term) {
        var s = term2String.get(term);
        string2Term.remove(s);
        term2String.remove(term);
        isTermEnabled.remove(term);
        changeSupport.firePropertyChange(s, term, null);
    }

    /// Sets the given `abbreviation` to `term` without checking of previous assignment.
    /// The abbreviation is set to be enabled.
    ///
    /// @param abbreviation the label of the abbreviation
    /// @param t a term
    public void forcePut(String abbreviation, JTerm t) {
        term2String.put(t, abbreviation);
        string2Term.put(abbreviation, t);

        setEnabled(t, true);
        changeSupport.firePropertyChange(abbreviation, null, t);
    }

    /// Register a [PropertyChangeListener] to be notified on abbrevation changes
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.addPropertyChangeListener(listener);
    }

    /// Deregister a [PropertyChangeListener] to be notified on abbrevation changes
    public void removePropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.removePropertyChangeListener(listener);
    }
}
