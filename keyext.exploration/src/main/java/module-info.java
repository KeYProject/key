import org.jspecify.annotations.NullMarked;

/**
 *
 * @author Alexander Weigl
 * @version 1 (31.03.24)
 */
@NullMarked module keyext.exploration {
    requires java.desktop;
    requires key.ui;
    requires key.core;
    requires org.jspecify;
    requires key.prover;
    requires key.ncore;
    requires org.key_project.util;
    requires dockingframes.common;
}
