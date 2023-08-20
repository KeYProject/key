/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.util.*;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Properties;
import java.util.Set;
import java.util.StringTokenizer;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 *
 */
public class ChoiceSettings extends AbstractSettings {
    private static final String KEY_DEFAULT_CHOICES = "[Choice]DefaultChoices";

    private static final String PROP_CHOICE_DEFAULT = "category2Default";
    private static final String PROP_CHOICE_CATEGORIES = "category2Choices";
    private HashMap<String, String> category2Default;


    /**
     * maps categories to a set of Strings(representing the choices which are options for this
     * category).
     */
    private Map<String, Set<String>> category2Choices = new LinkedHashMap<>();


    public ChoiceSettings() {
        category2Default = new LinkedHashMap<>();
    }


    public ChoiceSettings(Map<String, String> category2Default) {
        this.category2Default = new HashMap<>(category2Default);
    }


    public void setDefaultChoices(Map<String, String> category2Default) {
        var old = this.category2Default;
        this.category2Default = new HashMap<>(category2Default);
        firePropertyChange(PROP_CHOICE_DEFAULT, old, this.category2Default);
    }


    /**
     * returns a copy of the HashMap that maps categories to
     * their choices.
     */
    public Map<String, Set<String>> getChoices() {
        return Collections.unmodifiableMap(category2Choices);
    }

    /**
     * Returns an immutable view of the current mapping between category and default choices.
     * <p>
     * The method name is somewhat misleading.
     */
    @Nonnull
    public Map<String, String> getDefaultChoices() {
        return Collections.unmodifiableMap(category2Default);
    }


    /**
     * returns the current selected choices as an immutable set
     */
    @Nonnull
    public ImmutableSet<Choice> getDefaultChoicesAsSet() {
        return choiceMap2choiceSet(category2Default);
    }


    private static ImmutableSet<Choice> choiceMap2choiceSet(Map<String, String> ccc) {
        ImmutableList<Choice> choices = ImmutableSLList.nil();
        for (final Map.Entry<String, String> entry : ccc.entrySet()) {
            choices = choices.prepend(new Choice(new Name(entry.getValue()), entry.getKey()));
        }
        return DefaultImmutableSet.fromImmutableList(choices);
    }

    private void setChoiceCategories(HashMap<String, Set<String>> c2C) {
        var old = category2Choices;
        this.category2Choices = new HashMap<>(c2C);
        firePropertyChange(PROP_CHOICE_CATEGORIES, old, category2Choices);
    }

    /**
     * updates <code>category2Choices</code> if new entries are found in <code>choiceNS</code> or if
     * entries of <code>category2Choices</code> are no longer present in <code>choiceNS</code>
     *
     * @param remove remove entries not present in <code>choiceNS</code>
     */
    public void updateChoices(Namespace<Choice> choiceNS, boolean remove) {
        // Translate the given namespace into a map of 'string -> list[string]'
        HashMap<String, Set<String>> c2C = new LinkedHashMap<>();
        for (Choice c : choiceNS.allElements()) {
            Set<String> soc = c2C.computeIfAbsent(c.category(), k -> new LinkedHashSet<>());
            soc.add(c.name().toString());
        }

        // if there differences in the stored defaults, changed it accordingly
        if (!c2C.equals(category2Choices)) {
            var tmp = new HashMap<>(category2Choices);
            if (!remove) {
                tmp.putAll(c2C);
                setChoiceCategories(tmp);
            } else {
                setChoiceCategories(c2C);
            }
        }

        var defaultTmp = new HashMap<>(category2Default);
        for (var pair : category2Default.entrySet()) {
            var s = pair.getKey();
            var v = pair.getValue();
            // if key is known then the default value should exist
            if (category2Choices.containsKey(s)) {
                if (!category2Choices.get(s).contains(v)) {
                    defaultTmp.put(s, category2Choices.get(s).iterator().next());
                }
            } else {
                defaultTmp.remove(s);
            }
        }
        setDefaultChoices(defaultTmp);
    }

    /**
     * gets a Properties object and has to perform the necessary steps in order to change this
     * object in a way that it represents the stored settings
     */
    public void readSettings(Properties props) {
        String choiceSequence = props.getProperty(KEY_DEFAULT_CHOICES);
        // set choices
        if (choiceSequence != null) {
            StringTokenizer st = new StringTokenizer(choiceSequence, ",");
            while (st.hasMoreTokens()) {
                StringTokenizer st2 = new StringTokenizer(st.nextToken().trim(), "-");
                String category = st2.nextToken().trim();
                String def = st2.nextToken().trim();
                category2Default.put(category, def);

            }
        }
    }


    /**
     * implements the method required by the Settings interface. The settings are written to the
     * given Properties object. Only entries of
     * the form &lt; key &gt; = &lt; value &gt; (,&lt;
     * value &gt;)* are allowed.
     *
     ** @param props the Properties object where to write the
     *        settings as (key, value) pair
     */
    @Override
    public void writeSettings(Properties props) {
        StringBuilder choiceSequence = new StringBuilder();
        var keys = category2Default.keySet().stream().sorted().toArray(String[]::new);
        for (var key : keys) {
            if (choiceSequence.length() > 0) {
                choiceSequence.append(", ");
            }
            choiceSequence.append(key).append("-").append(category2Default.get(key));
        }
        props.setProperty(KEY_DEFAULT_CHOICES, choiceSequence.toString());
    }


    public ChoiceSettings updateWith(Iterable<Choice> sc) {
        for (final Choice c : sc) {
            category2Default.put(c.category(), c.name().toString());
        }
        return this;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        ChoiceSettings that = (ChoiceSettings) o;

        if (!Objects.equals(category2Default, that.category2Default)) {
            return false;
        }
        return Objects.equals(category2Choices, that.category2Choices);
    }

    @Override
    public int hashCode() {
        int result = category2Default != null ? category2Default.hashCode() : 0;
        result = 31 * result + (category2Choices != null ? category2Choices.hashCode() : 0);
        return result;
    }
}
