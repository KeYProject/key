package de.uka.ilkd.key.gui.extension.impl;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

public class ExtensionSettings extends AbstractPropertiesSettings {
    public final static String KEY_DISABLED = "[Extensions]disabled";
    private static final String DELIMITER = ",";

    public Collection<String> getForbiddenClasses() {
        return Arrays.asList(properties.getProperty(KEY_DISABLED, "")
                .split(DELIMITER));
    }

    public void setForbiddenClasses(Collection<String> seq) {
        properties.setProperty(KEY_DISABLED,
                seq.stream().collect(Collectors.joining(DELIMITER)));
        fireSettingsChange();
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
