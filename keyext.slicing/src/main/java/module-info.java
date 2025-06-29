import org.jspecify.annotations.NullMarked;

/**
 *
 * @author Alexander Weigl
 * @version 1 (31.03.24)
 */
@NullMarked module keyext.slicing {
    exports org.key_project.slicing;
    exports org.key_project.slicing.analysis;

    requires key.core;
    requires key.ncore;
    requires key.prover;
    requires org.key_project.util;
    requires org.slf4j;
    requires java.desktop;
    requires key.ui;
    requires org.jspecify;
    requires dockingframes.common;
    requires com.miglayout.core;
}
