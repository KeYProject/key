/**
 *
 * @author Alexander Weigl 
 * @version 1 (31.03.24)
 */
module org.key_project.ui {
    exports de.uka.ilkd.key.gui.extension.api;
    exports de.uka.ilkd.key.gui;
    exports de.uka.ilkd.key.gui.actions;
    exports de.uka.ilkd.key.gui.configuration;
    exports de.uka.ilkd.key.core;
    exports de.uka.ilkd.key.gui.fonticons;
    exports de.uka.ilkd.key.gui.help;
    exports de.uka.ilkd.key.ui.proof.io;
    exports de.uka.ilkd.key.gui.settings;
    exports de.uka.ilkd.key.ui.util;
    exports de.uka.ilkd.key.ui;
    exports de.uka.ilkd.key.gui.colors;
    exports de.uka.ilkd.key.gui.prooftree;
    exports de.uka.ilkd.key.gui.smt;
    exports de.uka.ilkd.key.gui.keyshortcuts;

    requires org.slf4j;
    requires java.desktop;
    requires org.key_project.core;
    requires java.prefs;
    requires org.jspecify;
    requires org.key_project.util;
    requires org.key_project.ncore;
    requires com.miglayout.core;
    requires com.miglayout.swing;
    requires ch.qos.logback.core;
    requires ch.qos.logback.classic;
    requires key.recoder;
    requires org.key_project.core.rifl;
    requires java.compiler;
    requires dockingframes.core;
    requires dockingframes.common;
    requires org.key_project.prover;
    requires org.antlr.antlr4.runtime;
    requires java.management;

    provides de.uka.ilkd.key.gui.extension.api.KeYGuiExtension with
            de.uka.ilkd.key.gui.originlabels.OriginTermLabelsExt,
            de.uka.ilkd.key.gui.extension.impl.HeatmapExt,
            de.uka.ilkd.key.gui.extension.impl.TestExtension,
            de.uka.ilkd.key.gui.docking.DockingLayout,
            de.uka.ilkd.key.gui.KeyboardTacletExtension,
            de.uka.ilkd.key.gui.nodeviews.ShowHashcodesExtension,
            de.uka.ilkd.key.gui.LogView,
            de.uka.ilkd.key.gui.plugins.javac.JavacExtension,
            de.uka.ilkd.key.gui.utilities.HeapStatusExt,
            de.uka.ilkd.key.gui.JmlEnabledKeysIndicator;

}