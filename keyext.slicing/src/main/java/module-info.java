/**
 *
 * @author Alexander Weigl
 * @version 1 (31.03.24)
 */
module keyext.slicing {
    requires org.key_project.core;
    requires org.key_project.ui;
    requires java.desktop;
    requires org.jspecify;
    requires org.slf4j;
    requires com.miglayout.core;
    requires org.key_project.util;
    requires org.key_project.ncore;
    requires dockingframes.common;
    requires dockingframes.core;
    exports org.key_project.slicing;
    exports org.key_project.slicing.analysis;
}