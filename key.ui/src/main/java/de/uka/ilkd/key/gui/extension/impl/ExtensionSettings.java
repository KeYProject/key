package de.uka.ilkd.key.gui.extension.impl;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

import java.util.Collection;
import java.util.Set;
import java.util.TreeSet;

public class ExtensionSettings extends AbstractPropertiesSettings {
    public final static String KEY_DISABLED = "[Extensions]disabled";
    private final PropertyEntry<Set<String>> forbiddenClasses = createStringSetProperty(KEY_DISABLED, "");

    public Collection<String> getForbiddenClasses() {
        return forbiddenClasses.get();
    }

    public void setForbiddenClasses(Collection<String> seq) {
        forbiddenClasses.set(new TreeSet<>(seq));
    }

    public PropertyEntry<Set<String>> forbiddenClasses() {
        return forbiddenClasses;
    }


    public void setForbiddenClass(Class type, boolean activated) {
        String text = type.getName();
        Collection<String> classes = getForbiddenClasses();
        if (activated) {
            classes.remove(text);
        } else {
            if (!classes.contains(text))
                classes.add(text);
        }
        setForbiddenClasses(classes);
    }
}
