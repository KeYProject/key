/**
 *
 * @author Alexander Weigl 
 * @version 1 (31.03.24)
 */
module keyext.slicing {
    exports org.key_project.slicing;
    exports org.key_project.slicing.analysis;
    requires org.key_project.core;
    requires org.key_project.ncore;
    requires org.key_project.prover;
    requires org.key_project.util;
    requires org.slf4j;
    requires java.desktop;
    requires org.key_project.ui;
    requires org.jspecify;
    requires dockingframes.common;
    requires com.miglayout.core;
}