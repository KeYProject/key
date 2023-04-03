package de.uka.ilkd.key.settings;

import java.util.*;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

public class ChoiceSettings implements Settings, Cloneable {

    private static final String DEFAULTCHOICES_KEY = "[Choice]DefaultChoices";
    private final LinkedList<SettingsListener> listenerList = new LinkedList<>();
    private HashMap<String, String> category2Default;


    /**
     * maps categories to a set of Strings(representing the choices which are options for this
     * category).
     */
    private HashMap<String, Set<String>> category2Choices =
        new LinkedHashMap<>();


    public ChoiceSettings() {
        category2Default = new LinkedHashMap<>();
    }


    public ChoiceSettings(HashMap<String, String> category2Default) {
        this.category2Default = category2Default;
    }


    public void setDefaultChoices(HashMap<String, String> category2Default) {
        HashMap<String, String> category2Defaultold = this.category2Default;
        this.category2Default = category2Default;
        if (category2Defaultold != null && !category2Defaultold.equals(category2Default)) {
            fireSettingsChanged();
        }
    }


    /**
     * returns a copy of the HashMap that maps categories to their choices.
     */
    @SuppressWarnings("unchecked")
    public HashMap<String, Set<String>> getChoices() {
        return (HashMap<String, Set<String>>) category2Choices.clone();
    }


    /**
     * returns a copy of the HashMap that maps categories to their currently selected choices.
     *
     * The method name is somewhat misleading.
     */
    @SuppressWarnings("unchecked")
    public HashMap<String, String> getDefaultChoices() {
        return (HashMap<String, String>) category2Default.clone();
    }


    /**
     * returns the current selected choices as set
     */
    public ImmutableSet<Choice> getDefaultChoicesAsSet() {
        return choiceMap2choiceSet(category2Default);
    }


    private static ImmutableSet<Choice> choiceMap2choiceSet(HashMap<String, String> ccc) {
        ImmutableList<Choice> choices = ImmutableSLList.nil();
        for (final Map.Entry<String, String> entry : ccc.entrySet()) {
            choices = choices.prepend(new Choice(new Name(entry.getValue()), entry.getKey()));
        }
        return DefaultImmutableSet.fromImmutableList(choices);
    }


    /**
     * updates <code>category2Choices</code> if new entries are found in <code>choiceNS</code> or if
     * entries of <code>category2Choices</code> are no longer present in <code>choiceNS</code>
     *
     * @param remove remove entries not present in <code>choiceNS</code>
     */
    public void updateChoices(Namespace<Choice> choiceNS, boolean remove) {
        Iterator<Choice> it = choiceNS.allElements().iterator();
        HashMap<String, Set<String>> c2C = new LinkedHashMap<>();
        Choice c;
        Set<String> soc;
        while (it.hasNext()) {
            c = it.next();
            if (c2C.containsKey(c.category())) {
                soc = c2C.get(c.category());
                soc.add(c.name().toString());
                c2C.put(c.category(), soc);
            } else {
                soc = new LinkedHashSet<>();
                soc.add(c.name().toString());
                c2C.put(c.category(), soc);
            }
        }
        if (!c2C.equals(category2Choices)) {
            if (remove) {
                category2Choices = c2C;
                fireSettingsChanged();
            } else {
                category2Choices.putAll(c2C);
                ProofSettings.DEFAULT_SETTINGS.saveSettings();
            }
        }
        for (final String s : getDefaultChoices().keySet()) {
            if (category2Choices.containsKey(s)) {
                if (!category2Choices.get(s).contains(category2Default.get(s))) {
                    category2Default.put(s, category2Choices.get(s).iterator().next());
                    fireSettingsChanged();
                }
            } else {
                category2Default.remove(s);
                fireSettingsChanged();
            }
        }
    }


    /**
     * sends the message that the state of this setting has been changed to its registered listeners
     * (not thread-safe)
     */
    protected void fireSettingsChanged() {
        Iterator<SettingsListener> it = listenerList.iterator();
        ProofSettings.DEFAULT_SETTINGS.saveSettings();
        while (it.hasNext()) {
            it.next().settingsChanged(new EventObject(this));
        }
    }


    /**
     * gets a Properties object and has to perform the necessary steps in order to change this
     * object in a way that it represents the stored settings
     */
    public void readSettings(Properties props) {
        String choiceSequence = props.getProperty(DEFAULTCHOICES_KEY);
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
     * given Properties object. Only entries of the form &lt; key &gt; = &lt; value &gt; (,&lt;
     * value &gt;)* are allowed.
     *
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    public void writeSettings(Properties props) {
        StringBuilder choiceSequence = new StringBuilder();
        for (final Map.Entry<String, String> entry : category2Default.entrySet()) {
            if (choiceSequence.length() > 0) {
                choiceSequence.append(" , ");
            }
            choiceSequence.append(entry.getKey()).append("-").append(entry.getValue());
        }
        props.setProperty(DEFAULTCHOICES_KEY, choiceSequence.toString());
    }


    public ChoiceSettings updateWith(Iterable<Choice> sc) {
        for (final Choice c : sc) {
            category2Default.put(c.category(), c.name().toString());
        }
        return this;
    }


    /**
     * adds a listener to the settings object
     *
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
        listenerList.add(l);
    }

    @Override
    public void removeSettingsListener(SettingsListener l) {
        listenerList.remove(l);
    }
}
