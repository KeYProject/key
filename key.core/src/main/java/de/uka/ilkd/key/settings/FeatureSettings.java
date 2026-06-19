/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.util.*;
import java.util.function.Consumer;

import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Feature flags for the selected and deselected of experimental features.
 * <p>
 * In the old days of KeY, we used to have {@code --experimental} flag, which was a bad idea.
 * You cannot control which feature you want to activate.
 * Instead, you are getting the full load of fun(ctionality). This class allows you to have more
 * fine-grained feature flags by defining feature flags which are controllable by the user.
 *
 * @author Alexander Weigl
 * @version 1 (04.12.23)
 */
public class FeatureSettings extends AbstractSettings {
    private static final Logger LOGGER = LoggerFactory.getLogger(FeatureSettings.class);
    private static final String CATEGORY = "Feature";

    /**
     * unstored, set by {@code --experimental}
     */
    private boolean activateAll = false;

    /**
     * persistent list of activated features
     */
    private final Set<String> activatedFeatures = new TreeSet<>();

    public FeatureSettings() {
        readFromSystemProperties();
    }

    public static boolean isFeatureActivated(Feature f) {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getFeatureSettings().isActivated(f);
    }

    public static boolean isFeatureActivated(String s) {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getFeatureSettings().isActivated(s);
    }

    /**
     * Helper function for notification on feature flag changes.
     *
     * @param feature the feature to be listening on
     * @param update a callback function which gets informed on changes with the new value
     */
    public static void on(Feature feature, Consumer<Boolean> update) {
        ProofIndependentSettings.DEFAULT_INSTANCE.getFeatureSettings().addPropertyChangeListener(
            feature.id, evt -> update.accept((Boolean) evt.getNewValue()));
    }

    /**
     * Helper function for notification on feature flag changes which also calls the consumer.
     *
     * @param feature the feature to be listening on
     * @param update a callback function which gets informed on changes with the new value
     */
    public static void onAndActivate(Feature feature, Consumer<Boolean> update) {
        on(feature, update);
        update.accept(isFeatureActivated(feature));
    }

    /**
     * Use the system properties ({@code -P FEATURE:XXX=true} to activate a feature from the command
     * line.
     */
    private void readFromSystemProperties() {
        var prefix = CATEGORY.toUpperCase() + ":";
        for (Map.Entry<Object, Object> entries : System.getProperties().entrySet()) {
            final var s = entries.getKey().toString();
            if (s.startsWith(prefix) && isTrue(entries.getValue())) {
                final var feature = s.substring(prefix.length());
                activate(feature);
                LOGGER.info("Activate feature: {}", feature);
            }
        }
    }

    /**
     * Checks if the given {@code value} represents something like to true.
     *
     * @return true, if {@code value} feels like a feature activation.
     */
    private boolean isTrue(Object value) {
        return switch (value.toString().toLowerCase()) {
            case "true", "yes", "on" -> true;
            default -> false;
        };
    }

    @Override
    public void readSettings(Properties props) {
        activatedFeatures.clear();
        var prefix = "[" + CATEGORY + "]";
        for (Map.Entry<Object, Object> entries : props.entrySet()) {
            final var s = entries.getKey().toString();
            if (s.startsWith(prefix) && isTrue(entries.getValue())) {
                final var feature = s.substring(prefix.length());
                activate(feature);
                LOGGER.info("Activate feature: {}", feature);
            }
        }
    }

    @Override
    public void writeSettings(Properties props) {
        var prefix = "[" + CATEGORY + "]";
        for (String activatedFeature : activatedFeatures) {
            props.put(prefix + activatedFeature, "true");
        }
    }

    @Override
    public void readSettings(@NonNull Configuration props) {
        activatedFeatures.clear();
        for (String s : props.getStringList(CATEGORY)) {
            activate(s);
        }
    }

    @Override
    public void writeSettings(@NonNull Configuration props) {
        props.set(CATEGORY, activatedFeatures.stream().toList());
    }

    public boolean isActivated(Feature f) {
        return isActivated(f.id);
    }

    private boolean isActivated(String id) {
        if (activateAll)
            return true;
        return activatedFeatures.contains(id);
    }

    /**
     * Activates the given feature {@code f}.
     */
    public void activate(Feature f) {
        activate(f.id);
    }

    /**
     * Activates the given feature by {@code id}.
     */
    private void activate(String id) {
        if (!isActivated(id)) {
            activatedFeatures.add(id);
            firePropertyChange(id, false, isActivated(id));
        }
    }

    /**
     * Deactivates the given feature {@code f}.
     */
    public void deactivate(Feature f) {
        deactivate(f.id);
    }

    /**
     * Deactivates the given feature by {@code id}.
     */
    private void deactivate(String id) {
        if (isActivated(id)) {
            firePropertyChange(id, true, isActivated(id));
            activatedFeatures.remove(id);
        }
    }

    public void setActivateAll(boolean b) {
        activateAll = b;
    }

    public boolean isActivateAll() {
        return activateAll;
    }

    public static Feature createFeature(String id) {
        return createFeature(id, "", true);
    }

    public static Feature createFeature(String id, String doc) {
        return new Feature(id, doc, true);
    }

    public static Feature createFeature(String id, String doc, boolean restartRequired) {
        return new Feature(id, doc, restartRequired);
    }

    public record Feature(String id, String documentation, boolean restartRequired) {

        public static final List<Feature> FEATURES = new ArrayList<>();

        public Feature {
            FEATURES.add(this);
        }
    }
}
