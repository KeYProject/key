/**
 * This package provides a facility for a settings UI.
 * <p>
 * The settings UI consists out of a tree on left and customizable panes on the right.
 * <p>
 * You can participate on the default settings by adding a
 * {@link de.uka.ilkd.key.gui.settings.SettingsProvider} to
 * {@link de.uka.ilkd.key.gui.settings.SettingsManager#getInstance()}. The typical built-in settings
 * are already register within this method.
 * <p>
 * Also you could consider using an extension:
 * {@link de.uka.ilkd.key.gui.extension.api.KeYGuiExtension.Settings}.
 *
 * @author Alexander Weigl
 */
package de.uka.ilkd.key.gui.settings;
