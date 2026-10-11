/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Proxy;
import java.util.List;
import javafx.scene.Node;

import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * The test-generation settings entry, FX port of {@code TestgenOptionsPanel} (Swing
 * TestgenOptionsPanel.java:14-157) as a {@code SettingsProviderF}: the symbolic-execution/macro
 * options, the maximal unwinds and concurrent SMT-process numbers, the output folder, and the
 * duplicate/RFL/invariant/post-condition toggles — reading and writing the global singleton
 * {@link TestGenerationSettingsF} (TestgenOptionsPanel.getPanel/getDescription/applySettings,
 * TestgenOptionsPanel.java:134-157). The widgets live in {@link TestgenOptionsPanelF} (shared
 * with the embedded panel of the run dialog).
 * <p>
 * <b>KNOWN-SIMPLIFIED (proxy provider):</b> {@code SettingsProviderF.getPanel/apply} are declared
 * with a {@code MainWindowF} parameter, and any {@code MainWindowF} type use in this module
 * forces javac to complete the class file, which fails ("Cannot attach type annotations ... to
 * MainWindowF.lastEnvironment: class file for de.uka.ilkd.key.control.KeYEnvironment not
 * found"). The provider is therefore a {@link java.lang.reflect.Proxy} implementing
 * {@code SettingsProviderF} without naming the window type at compile time; the window arrives as
 * a plain {@code Object} argument of the reflective dispatch and is forwarded to
 * {@link TestgenExtensionF#captureWindow(Object)} (the extension's only compile-safe window
 * channel).
 * <p>
 * <b>KNOWN-SIMPLIFIED (panel):</b> the Swing panel subclasses the Swing {@code SettingsPanel}
 * base (row/validator/chooser helpers) and installs change listeners that write into a working
 * copy of the settings as the user edits; the FX port keeps the edits in the widgets
 * ({@code live=false} mode of {@link TestgenOptionsPanelF}) and reads them in {@code apply} only
 * (leaving the dialog through OK/Apply is the only path that persists, so the result is
 * identical).
 */
@NullMarked
final class TestgenSettingsProviderF {

    private TestgenSettingsProviderF() {
    }

    /**
     * Creates the {@link SettingsProviderF} entry (a reflective {@link Proxy}) for the given
     * extension, forwarding the main window of every panel access to
     * {@link TestgenExtensionF#captureWindow(Object)}.
     *
     * @param extension the owning extension, notified of the main window
     * @return the settings provider, never {@code null}
     */
    static SettingsProviderF create(TestgenExtensionF extension) {
        return (SettingsProviderF) Proxy.newProxyInstance(SettingsProviderF.class
                .getClassLoader(),
            new Class<?>[] { SettingsProviderF.class },
            new SettingsState(extension));
    }

    /**
     * The {@link InvocationHandler} of the settings provider: dispatching the
     * {@code SettingsProviderF} methods (routed by name, mirroring the Swing original's
     * semantics) over the {@link TestgenOptionsPanelF} widgets.
     * <p>
     * The panel is deliberately built lazily: every {@code javafx.scene.control.Control} triggers
     * the FX toolkit in its class initializer ("Toolkit not initialized"), so neither the
     * provider proxy nor the extension must touch Controls until the settings panel is really
     * opened inside the running app.
     */
    private static final class SettingsState implements InvocationHandler {

        private final TestgenExtensionF extension;

        /** the options panel widgets; {@code null} until the panel is first opened */
        private @Nullable TestgenOptionsPanelF optionsPanel;

        SettingsState(TestgenExtensionF extension) {
            this.extension = extension;
        }

        /** The SettingsProviderF dispatch of the reflective provider. */
        @Override
        public Object invoke(Object proxy, java.lang.reflect.Method method, Object[] args) {
            switch (method.getName()) {
                case "getDescription" -> {
                    // extension: MP9.5 — Swing TestgenOptionsPanel.getDescription
                    // (TestgenOptionsPanel.java:134)
                    return "TestGen";
                }
                case "getPanel" -> {
                    // extension: MP9.5 — Swing TestgenOptionsPanel.getPanel
                    // (TestgenOptionsPanel.java:139-151): re-read the global settings.
                    if (args != null && args.length > 0 && args[0] != null) {
                        extension.captureWindow(args[0]);
                    }
                    return panel();
                }
                case "apply" -> {
                    // extension: MP9.5 — Swing TestgenOptionsPanel.applySettings
                    // (TestgenOptionsPanel.java:153): write the widget states back.
                    if (args != null && args.length > 0 && args[0] != null) {
                        extension.captureWindow(args[0]);
                    }
                    applySettings();
                    return null;
                }
                case "getChildProviders" -> {
                    return List.of();
                }
                case "getPriorityOfSettings" -> {
                    return 0;
                }
                case "contains" -> {
                    // the SettingsProviderF default: description substring match.
                    String substring =
                        args == null || args.length == 0 || args[0] == null ? null
                                : args[0].toString();
                    return substring != null && !substring.isEmpty()
                            && "TestGen".toLowerCase().contains(substring.toLowerCase());
                }
                case "equals" -> {
                    return args != null && args.length == 1 && args[0] == proxy;
                }
                case "hashCode" -> {
                    return System.identityHashCode(proxy);
                }
                case "toString" -> {
                    return "TestGenerationSettingsProvider(proxy)";
                }
                default -> {
                }
            }
            return null;
        }

        /** Builds (once) and returns the options panel, re-reading the global settings. */
        private Node panel() {
            if (optionsPanel == null) {
                optionsPanel = new TestgenOptionsPanelF(false);
            }
            optionsPanel.readFromSettings();
            return optionsPanel.getNode();
        }

        /** Writes the widget states back into the global settings singleton. */
        private void applySettings() {
            if (optionsPanel == null) {
                // the panel was never opened, nothing was edited to persist.
                return;
            }
            optionsPanel.applySettings();
        }
    }
}
