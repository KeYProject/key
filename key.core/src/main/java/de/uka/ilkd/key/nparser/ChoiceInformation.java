package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Namespace;
import javax.annotation.Nonnull;

import java.util.*;

/**
 * A POJO representing the information on choices in ASTs.
 * <p>
 * Notion: A choice, e.g. {@code permission:on} contains a category  {@code permission}
 * and an option {@code on}.
 *
 * @author Alexander Weigl
 * @version 1 (12/5/19)
 */
public class ChoiceInformation {
    /**
     * A map from a found category to a set of possible (defined) options.
     */
    private final Map<String, Set<String>> foundChoicesAndOptions = new HashMap<>();

    /**
     * This set contains categories were an options was activated.
     * Helps to prevent double activation of contradictory options.
     */
    private final HashSet<String> activatedChoicesCategories = new LinkedHashSet<>();

    /**
     * This set contains the activated choices.
     */
    private final Set<Choice> activatedChoices = new HashSet<>();

    /**
     * This namespace contains all found choices.
     */
    private final Namespace<Choice> choices;

    /**
     * This map contains the default option for every category.
     */
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
