import de.uka.ilkd.key.caching.CachingExtension;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import org.jspecify.annotations.NullMarked;

/**
 *
 * @author Alexander Weigl 
 * @version 1 (31.03.24)
 */
@NullMarked
module keyext.caching {
    requires java.desktop;
    requires key.ui;
    requires key.core;
    requires key.ncore;
    requires key.prover;
    requires keyext.slicing;
    requires org.slf4j;
    requires org.jspecify;
    requires org.key_project.util;
    requires com.miglayout.core;

    provides KeYGuiExtension with CachingExtension;
}