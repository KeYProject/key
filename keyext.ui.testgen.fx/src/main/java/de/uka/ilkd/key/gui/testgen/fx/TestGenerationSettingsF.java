/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A typed view on the global {@code TestGenerationSettings} singleton of {@code key.core.testgen}
 * for the FX module.
 * <p>
 * <b>NOT part of the SPI:</b> {@code key.core.testgen} is not on the compile classpath of this
 * module (the frozen {@code build.gradle} only exposes {@code key.ui.fx} and the Swing
 * {@code keyext.ui.testgen} to the compiler; key.core/key.core.testgen arrive on the runtime
 * classpath), so the settings bean is reached through plain reflection. The accessors mirror the
 * Swing {@code TestgenOptionsPanel} (TestgenOptionsPanel.java:134-157) and the command line
 * properties {@code TestgenOptionsPanel.saveSettingsToFile}, i.e. the getters/setters the Swing
 * panel reads and writes.
 */
@NullMarked
final class TestGenerationSettingsF {

    private static final Logger LOGGER = LoggerFactory.getLogger(TestGenerationSettingsF.class);

    private static final String SETTINGS_CLASS = "de.uka.ilkd.key.testgen.TestGenerationSettings";

    /** the global singleton instance, {@code null} if the class is not present at runtime. */
    private final @Nullable Object instance;

    TestGenerationSettingsF() {
        this.instance = instance();
    }

    /**
     * @return the {@code TestGenerationSettings.getInstance()} singleton or {@code null} when the
     *         key.core.testgen classes are unavailable (should not happen in the app runtime)
     */
    private static @Nullable Object instance() {
        try {
            Class<?> settingsClass = Class.forName(SETTINGS_CLASS);
            return settingsClass.getMethod("getInstance").invoke(null);
        } catch (ReflectiveOperationException e) {
            LOGGER.warn("TestGenerationSettings is not available", e);
            return null;
        }
    }

    /** Swing TestgenOptionsPanel: {@code settings.getApplySymbolicExecution()}. */
    boolean applySymbolicEx() {
        return bool("getApplySymbolicExecution");
    }

    /** Swing TestgenOptionsPanel: {@code settings.getMaximalUnwinds()}. */
    int maxUnwinds() {
        return intOf("getMaximalUnwinds");
    }

    /** Swing TestgenOptionsPanel: {@code settings.invariantForAll()}. */
    boolean invariantForAll() {
        return bool("invariantForAll");
    }

    /** Swing TestgenOptionsPanel: {@code settings.includePostCondition()}. */
    boolean includePostCondition() {
        return bool("includePostCondition");
    }

    /** Swing TestgenOptionsPanel: {@code settings.getNumberOfProcesses()}. */
    int processes() {
        return intOf("getNumberOfProcesses");
    }

    /** Swing TestgenOptionsPanel: {@code settings.getOutputFolderPath()}. */
    String outputFolderPath() {
        Object value = invokeObject("getOutputFolderPath");
        return value == null ? "" : value.toString();
    }

    /** Swing TestgenOptionsPanel: {@code settings.removeDuplicates()}. */
    boolean removeDuplicates() {
        return bool("removeDuplicates");
    }

    /** Swing TestgenOptionsPanel: {@code settings.isUseRFL()}. */
    boolean useRFL() {
        return bool("isUseRFL");
    }

    /** Swing TestgenOptionsPanel.applySettings: {@code settings.setApplySymbolicExecution}. */
    void setApplySymbolicEx(boolean value) {
        invoke("setApplySymbolicExecution", value);
    }

    /** Swing TestgenOptionsPanel.applySettings: {@code settings.setInvariantForAll}. */
    void setInvariantForAll(boolean value) {
        invoke("setInvariantForAll", value);
    }

    /** Swing TestgenOptionsPanel.applySettings: {@code settings.setIncludePostCondition}. */
    void setIncludePostCondition(boolean value) {
        invoke("setIncludePostCondition", value);
    }

    /** Swing TestgenOptionsPanel.applySettings: {@code settings.setMaxUnwinds}. */
    void setMaxUnwinds(int value) {
        invoke("setMaxUnwinds", value);
    }

    /** Swing TestgenOptionsPanel.applySettings: {@code settings.setConcurrentProcesses}. */
    void setConcurrentProcesses(int value) {
        invoke("setConcurrentProcesses", value);
    }

    /** Swing TestgenOptionsPanel.applySettings: {@code settings.setOutputPath}. */
    void setOutputPath(String value) {
        invoke("setOutputPath", value);
    }

    /** Swing TestgenOptionsPanel.applySettings: {@code settings.setRemoveDuplicates}. */
    void setRemoveDuplicates(boolean value) {
        invoke("setRemoveDuplicates", value);
    }

    /** Swing TestgenOptionsPanel.applySettings: {@code settings.setUseRFL}. */
    void setUseRFL(boolean value) {
        invoke("setUseRFL", value);
    }

    // ------------------------------------------------------------------ reflection

    private boolean bool(String getter) {
        Object value = invokeObject(getter);
        return value instanceof Boolean b && b;
    }

    private int intOf(String getter) {
        Object value = invokeObject(getter);
        return value instanceof Number n ? n.intValue() : 0;
    }

    private @Nullable Object invokeObject(String method) {
        Object target = instance;
        if (target == null) {
            return null;
        }
        try {
            return target.getClass().getMethod(method).invoke(target);
        } catch (ReflectiveOperationException | RuntimeException e) {
            LOGGER.warn("Could not read TestGenerationSettings.{}", method, e);
            return null;
        }
    }

    private void invoke(String method, Object value) {
        Object target = instance;
        if (target == null) {
            LOGGER.warn("TestGenerationSettings not available, ignoring {}({})", method, value);
            return;
        }
        try {
            target.getClass().getMethod(method, primitiveType(value)).invoke(target, value);
        } catch (ReflectiveOperationException | RuntimeException e) {
            LOGGER.warn("Could not write TestGenerationSettings.{}", method, e);
        }
    }

    /** maps the boxed argument to the primitive parameter type of the settings setter. */
    private static Class<?> primitiveType(Object value) {
        if (value instanceof Boolean) {
            return boolean.class;
        }
        if (value instanceof Integer) {
            return int.class;
        }
        return value.getClass();
    }
}
