package org.key_project.javaeditor.util;

/**
 * Listens for changes on {@link PreferenceUtil}.
 * <p>
 * Implementations are registered via extension point {@link PreferenceUtil#LISTENER_EXTENSION_POINT}.
 * @author Martin Hentschel
 */
public interface IPreferenceListener {
   public void extensionsEnabledStateChanged(boolean newEnabled);
   
   public void extensionEnabledStateChanged(String id, boolean newEnabled);
}
