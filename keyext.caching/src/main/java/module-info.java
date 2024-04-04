import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.plugins.caching.CachingExtension;

/**
 *
 * @author Alexander Weigl
 * @version 1 (31.03.24)
 */
module keyext.caching{requires org.key_project.ui;requires org.key_project.core;requires org.slf4j;requires org.jspecify;requires java.desktop;requires org.key_project.util;requires org.key_project.ncore;requires keyext.slicing;requires com.miglayout.core;

provides KeYGuiExtension with CachingExtension;}
