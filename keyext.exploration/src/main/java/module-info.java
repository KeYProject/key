import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;

/**
 *
 * @author Alexander Weigl
 * @version 1 (31.03.24)
 */
module keyext.exploration{requires transitive org.key_project.ui;requires org.key_project.core;requires org.jspecify;requires java.desktop;requires org.key_project.ncore;requires org.key_project.util;requires dockingframes.common;

provides KeYGuiExtension with org.key_project.exploration.ExplorationExtension;}
