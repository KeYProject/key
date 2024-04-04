import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;

/**
 *
 * @author Alexander Weigl
 * @version 1 (31.03.24)
 */
module keyext.ui.testgen{requires java.desktop;requires org.key_project.ui;requires org.slf4j;requires org.key_project.core;requires org.key_project.core.testgen;requires org.jspecify;

provides KeYGuiExtension with de.uka.ilkd.key.gui.testgen.TestgenExtension;}
