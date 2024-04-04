import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;

/**
 *
 * @author Alexander Weigl
 * @version 1 (31.03.24)
 */
module keyext.proofmanagement{requires org.key_project.ui;requires org.jspecify;requires java.desktop;requires org.slf4j;requires org.key_project.core;requires org.key_project.util;requires org.key_project.ncore;
/* not available requires ST4; */


provides KeYGuiExtension with org.key_project.proofmanagement.ProofManagementExt;}
