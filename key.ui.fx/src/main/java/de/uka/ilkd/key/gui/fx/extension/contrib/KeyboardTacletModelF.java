/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import org.key_project.prover.rules.RuleApp;

/**
 * The prefix-matching model of the keyboard-taclet panel, JavaFX port of the package-private
 * {@code KeyboardTacletModel} nested at the end of the Swing original
 * (key.ui/src/main/java/de/uka/ilkd/key/gui/KeyboardTacletExtension.java:388-534). The port is
 * verbatim: the taclet names are grouped into an application list keyed by rule name
 * ({@code HashMap}, so the iteration order of {@link #getPrefixTable()} /
 * {@link #getFirstMatchingTacletApp()} keeps the Swing quirks), a clash-free prefix table is
 * built over the rule names ({@link #buildPrefixTable}), and keyboard input is reduced to
 * {@link #processChar}: digits set the selection index <em>and</em> are appended to the current
 * prefix (Swing KeyboardTacletExtension.java:467-475), escape resets and backspace shortens the
 * prefix.
 * <p>
 * Property names {@link #PROP_CURRENT_PREFIX} / {@link #PROP_CURRENT_POS} and the
 * {@link PropertyChangeSupport} wiring are kept from the Swing original so the panel (and any
 * test) can observe prefix changes exactly like Swing. {@code java.beans} is already used inside
 * the FX module (e.g. {@code StrategySelectionDriver}), the model itself is toolkit-free.
 */
class KeyboardTacletModelF {
    public static final String PROP_CURRENT_PREFIX = "currentPrefix";
    public static final String PROP_CURRENT_POS = "currentPos";
    private final Map<String, List<RuleApp>> taclets;
    private final Map<String, String> prefixTable;
    private final PropertyChangeSupport propertyChangeSupport = new PropertyChangeSupport(this);

    private String currentPrefix;
    private int currentPos;

    KeyboardTacletModelF(List<RuleApp> taclets) {
        reset();
        this.taclets = new HashMap<>();
        List<String> seq = new ArrayList<>(taclets.size());
        for (RuleApp t : taclets) {
            String n = t.rule().name().toString();
            seq.add(n);
            List<RuleApp> appSeq = this.taclets.computeIfAbsent(n, it -> (new ArrayList<>(5)));
            appSeq.add(t);
        }

        prefixTable = buildPrefixTable(seq);
    }

    static int getClashFreePrefix(String unique, Collection<String> strings) {
        return strings.stream().filter(it -> !it.equals(unique))
                .mapToInt(c -> getPrefixLength(unique, c)).max().orElse(0);
    }

    static int getPrefixLength(String a, String b) {
        int i = 0;
        for (; i < Math.min(a.length(), b.length()) && (a.charAt(i) == b.charAt(i)
                || !charValid(a.charAt(i)) || !charValid(b.charAt(i))); i++) {
            // empty
        }
        return i;
    }

    static Map<String, String> buildPrefixTable(List<String> seq) {
        Map<String, String> table = new HashMap<>();
        for (String name : seq) {
            int prefixL = getClashFreePrefix(name, seq);
            table.put(name.substring(0, Math.min(prefixL + 1, name.length())), name);
        }
        return table;
    }

    // Swing parity: charValid always returns true (the original restriction is commented out,
    // KeyboardTacletExtension.java:440-442), so every typed character extends the prefix
    static boolean charValid(char c) {
        return true; // return ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z');
    }

    public void addPropertyChangeListener(PropertyChangeListener listener) {
        propertyChangeSupport.addPropertyChangeListener(listener);
    }

    public void removePropertyChangeListener(PropertyChangeListener listener) {
        propertyChangeSupport.removePropertyChangeListener(listener);
    }

    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        propertyChangeSupport.addPropertyChangeListener(propertyName, listener);
    }

    public void processChar(char c) {
        switch (c) {
            case '\u001B' -> // escape
                reset();
            case '\b' -> {
                if (currentPrefix.length() <= 1) {
                    setCurrentPrefix("");
                } else {
                    setCurrentPrefix(currentPrefix.substring(0, currentPrefix.length() - 1));
                }
            }
            default -> {
                if ('0' <= c && c <= '9') {
                    setCurrentPos(c - '0');
                }
                if (charValid(c)) {
                    setCurrentPrefix(currentPrefix + c);
                }
            }
        }
    }

    public int getCurrentPos() {
        return currentPos;
    }

    public void setCurrentPos(int currentPos) {
        int old = this.currentPos;
        this.currentPos = currentPos;
        propertyChangeSupport.firePropertyChange(PROP_CURRENT_POS, old, currentPos);
    }

    private void reset() {
        setCurrentPrefix("");
        setCurrentPos(-1);
    }

    public Optional<RuleApp> getSelectedTacletsApp() {
        List<RuleApp> t = taclets.get(prefixTable.get(currentPrefix));
        if (t != null && t.size() == 1 || (currentPos >= 0 && currentPos <= taclets.size())) {
            assert t != null;
            return Optional.of(t.get(Math.max(0, currentPos)));
        }
        return Optional.empty();
    }

    public Optional<RuleApp> getFirstMatchingTacletApp() {
        for (String prefix : getPrefixTable().keySet()) {
            if (prefix.startsWith(currentPrefix)) {
                String tacletName = prefixTable.get(prefix);
                List<RuleApp> apps = taclets.get(tacletName);
                return Optional.of(apps.get(0));
            }
        }
        return Optional.empty();
    }

    public Map<String, String> getPrefixTable() {
        return prefixTable;
    }

    public String getCurrentPrefix() {
        return currentPrefix;
    }

    public void setCurrentPrefix(String currentPrefix) {
        String old = this.currentPrefix;
        this.currentPrefix = currentPrefix;
        propertyChangeSupport.firePropertyChange(PROP_CURRENT_PREFIX, old, currentPrefix);
    }

    public Collection<String> getTacletNames() {
        return prefixTable.values().stream().sorted().collect(Collectors.toList());
    }

    public Map<String, List<RuleApp>> getTaclets() {
        return taclets;
    }
}
