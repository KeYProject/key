/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.javac;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

/**
 * Settings for the javac extention.
 *
 * @author Daniel Grévent
 */
public class JavacSettings extends AbstractPropertiesSettings {

    /**
     * The name of the category in the settings.
     */
    public static final String CATEGORY = "Javac Extension";

    /**
     * Config key for {@link #useProcessors}.
     */
    private static final String KEY_USE_PROCESSORS = "useProcessors";

    /**
     * Config key for {@link #processors}.
     */
    private static final String KEY_PROCESSORS = "processors";

    /**
     * Config key for {@link #classPaths}.
     */
    private static final String KEY_CLASS_PATHS = "classPaths";

    /**
     * The type annotation processors to be run.
     */
    private final PropertyEntry<Boolean> useProcessors =
        createBooleanProperty(KEY_USE_PROCESSORS, false);

    /**
     * The type annotation processors to be run.
     */
    private final PropertyEntry<String> processors =
        createStringProperty(KEY_PROCESSORS, "");

    /**
     * Additional class paths, needed for example by annotation processors
     */
    private final PropertyEntry<String> classPaths =
        createStringProperty(KEY_CLASS_PATHS, "");

    public JavacSettings() {
        super(CATEGORY);
    }

    /**
     * @param useProcessors if the annotation processors should be run
     */
    public void setUseProcessors(boolean useProcessors) {
        this.useProcessors.set(useProcessors);
    }

    /**
     * @param processor the annotation processors to run
     */
    public void setProcessors(String processor) {
        this.processors.set(processor);
    }

    /**
     * @param paths the additional class paths
     */
    public void setClassPaths(String paths) {
        this.classPaths.set(paths);
    }

    /**
     * @return true iff the annotation processors should be used
     */
    public boolean getUseProcessors() {
        return useProcessors.get();
    }

    /**
     * @return the annotation processors separated by newlines
     */
    public String getProcessors() {
        return processors.get();
    }

    /**
     * @return the additional class paths separated by newlines
     */
    public String getClassPaths() {
        return classPaths.get();
    }
}
