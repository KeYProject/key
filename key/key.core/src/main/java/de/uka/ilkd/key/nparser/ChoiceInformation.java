package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Namespace;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (12/5/19)
 */
public class ChoiceInformation {
    private final Map<String, Set<String>> foundChoicesAndOptions = new HashMap<>();
    private final HashSet<String> activatedChoicesCategories = new LinkedHashSet<>();
    private final Set<Choice> activatedChoices = new HashSet<>();
    private final Namespace<Choice> choices;
    private final Map<String, String> defaultOptions = new TreeMap<>();

    public ChoiceInformation() {
        this(new Namespace<>());
    }

    public ChoiceInformation(Namespace<Choice> choices) {
        this.choices = choices;
    }

    public Map<String, Set<String>> getFoundChoicesAndOptions() {
        return foundChoicesAndOptions;
    }

    public HashSet<String> getActivatedChoicesCategories() {
        return activatedChoicesCategories;
    }

    public Set<Choice> getActivatedChoices() {
        return activatedChoices;
    }

    public Namespace<Choice> getChoices() {
        return choices;
    }

    public void setDefaultOption(String category, String choice) {
        defaultOptions.put(category, category + ":" + choice);
    }

    public Map<String, String> getDefaultOptions() {
        return defaultOptions;
    }
}
