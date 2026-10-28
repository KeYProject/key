/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.help;

import java.awt.Desktop;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.function.Consumer;
import javafx.application.Application;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.input.KeyCombination;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A gate to the KeY documentation system.
 * <p>
 * JavaFX port of {@code de.uka.ilkd.key.gui.help.HelpFacade} (Swing {@code HelpFacade.java}).
 * Provides the facility to open the documentation at the press of F1. The opened page is
 * determined context-sensitively by the currently focused node and its parent chain: the first
 * class carrying a {@link HelpInfoF} annotation wins; without any annotation the main
 * documentation page is opened.
 * <p>
 * Port notes and deviations from the Swing original:
 * <ul>
 * <li>The browser is opened via the JavaFX {@link Application#getHostServices()} (handed over by
 * {@code MainApplication}) with a {@link Desktop#browse(URI)} fallback — the Swing original uses
 * {@code SwingUtil.browse} ({@code HelpFacade.java:60-66}), which lives in the Swing-only module
 * {@code key.ui} and is therefore not reachable from {@code key.ui.fx}.</li>
 * <li>The Swing base-URL override reads {@code System.getProperty("KEY_HELP_URL")} for the null
 * check but {@code System.getProperty(KEY_HELP_URL)} (i.e. {@code "key.help.url"}) for the value
 * ({@code HelpFacade.java:54-58}) — with the documented property {@code key.help.url} the check
 * never fires. The port reads {@code "key.help.url"} consistently.</li>
 * <li>The Swing {@code OpenHelpAction} carries a TODO: its {@code ActionEvent} source is always
 * the root pane, so F1 always opened the main page ({@code HelpFacade.java:154-158} comment).
 * The FX F1 handler (registered in {@code MainWindowF.handleMainWindowKeyPressed}) instead walks
 * the focus owner's parent chain and only falls back to the main page — the intended behavior,
 * without the Swing bug.</li>
 * <li>{@code HelpFacade.createHelpButton} / {@code createHelpAction}
 * ({@code HelpFacade.java:133-152})
 * create dockable-title buttons — the FX docking framework has no title-action API yet, so they
 * are deliberately not ported (the parallel dock-actions work will host them).</li>
 * </ul>
 */
public final class HelpFacadeF {
    private static final Logger LOGGER = LoggerFactory.getLogger(HelpFacadeF.class);

    /**
     * System property key for setting the base url of the help system (Swing
     * {@code HelpFacade.KEY_HELP_URL}).
     */
    public static final String KEY_HELP_URL = "key.help.url";

    /**
     * The base url of the help system (Swing {@code HelpFacade.HELP_BASE_URL}, {@code
     * HelpFacade.java:52}); overridable via the {@link #KEY_HELP_URL} property.
     */
    public static String HELP_BASE_URL = "https://keyproject.github.io/key-docs/";

    static {
        if (System.getProperty(KEY_HELP_URL) != null) {
            HELP_BASE_URL = System.getProperty(KEY_HELP_URL);
        }
    }

    /**
     * The running application handed over by the {@code MainApplication} (see the class javadoc);
     * {@code null} until then, in which case {@link Desktop} is used.
     */
    private static Application application;

    /**
     * The browser-opening seam; replaceable for the self test so no real browser is launched
     * during verification.
     */
    private static Consumer<String> browserOpener = HelpFacadeF::openInSystemBrowser;

    private HelpFacadeF() {
    }

    /**
     * Hands the application's host services to this facade; called by {@code MainApplication}
     * during startup.
     *
     * @param application the running {@link Application}
     */
    public static void setHostServices(Application runningApplication) {
        application = runningApplication;
    }

    private static void openInSystemBrowser(String url) {
        if (application != null) {
            application.getHostServices().showDocument(url);
            return;
        }
        try {
            Desktop.getDesktop().browse(new URI(url));
        } catch (IOException | URISyntaxException | UnsupportedOperationException
                | IllegalStateException e) {
            LOGGER.warn("Failed to open help in browser", e);
        }
    }

    /**
     * Opens the key documentation website in the default system browser (Swing
     * {@code HelpFacade.openHelp}, {@code HelpFacade.java:71-73}).
     */
    public static void openHelp() {
        openHelpInBrowser(HELP_BASE_URL);
    }

    /**
     * Opens the specified subpage of the KeY documentation website in the default system browser
     * (Swing {@code HelpFacade.openHelp(String)}, {@code HelpFacade.java:80-89}).
     *
     * @param path a valid suffix to the current URI
     */
    public static void openHelp(String path) {
        if (path.startsWith("https://")) {
            openHelpInBrowser(path);
            return;
        }
        if (path.startsWith("/")) {
            path = path.substring(1);
        }
        openHelpInBrowser(HELP_BASE_URL + path);
    }

    /**
     * Tries to find the documentation of the given node and opens it (Swing
     * {@code HelpFacade.openHelp(Component)}, {@code HelpFacade.java:99-107}, the component
     * counterpart being the parent chain {@code Component.getParent()}).
     * <p>
     * The documentation is determined by following the parents to the root and checking for
     * {@link HelpInfoF} on the node classes. Without any annotated class the main documentation
     * page is opened.
     *
     * @param node the focused node, may be {@code null}
     */
    public static void openHelp(Node node) {
        while (node != null) {
            if (openHelpOfClass(node.getClass())) {
                return;
            }
            node = node.getParent();
        }
        openHelp();
    }

    /**
     * Opens documentation given for the given class (Swing
     * {@code HelpFacade.openHelpOfClass}, {@code HelpFacade.java:117-124}). The class needs to
     * be annotated with {@link HelpInfoF}.
     *
     * @param clazz non-null class instance
     * @return whether documentation was found and opened
     */
    public static boolean openHelpOfClass(Class<?> clazz) {
        HelpInfoF help = clazz.getAnnotation(HelpInfoF.class);
        if (help != null) {
            openHelpInBrowser(HELP_BASE_URL + help.path());
            return true;
        }
        return false;
    }

    /**
     * Opens the documentation for the currently focused node at the press of F1 (Swing trigger:
     * {@code MainWindow.java:300-302} registers {@code HelpFacade.ACTION_OPEN_HELP} on the root
     * pane with the F1 accelerator set in {@code HelpFacade.OpenHelpAction}, {@code
     * HelpFacade.java:159-174}).
     * <p>
     * <em>Registration note:</em> {@code MainWindowF} handles F1 in its scene key handler
     * ({@code handleMainWindowKeyPressed}, next to the Ctrl+Space/Escape action keys); this
     * alternative registration stays available for additional scenes (e.g. floating dock
     * stages) that lack a shared key handler. Register F1 at most once per scene, otherwise the
     * accelerator (which is processed before the normal key dispatch) would shadow the handler.
     *
     * @param scene the scene to register the help accelerator for
     */
    public static void installAccelerator(Scene scene) {
        // Scene.getAccelerators() is an ObservableMap<KeyCombination, Runnable> — the runnable is
        // registered under its F1 key combination (Swing OpenHelpAction accelerator
        // KeyStroke.getKeyStroke(VK_F1, 0), HelpFacade.java:164)
        scene.getAccelerators().put(KeyCombination.valueOf("F1"),
            () -> openHelp(scene.getFocusOwner()));
    }

    /**
     * Resolves the documentation URL for the given class (the URL-returning variant of
     * {@link #openHelpOfClass(Class)}): the {@link HelpInfoF} path appended to the base URL, or
     * {@code null} when the class carries no annotation.
     *
     * @param clazz non-null class instance
     * @return the documentation URL or {@code null}
     */
    public static String helpUrlOfClass(Class<?> clazz) {
        HelpInfoF help = clazz.getAnnotation(HelpInfoF.class);
        if (help == null) {
            return null;
        }
        String path = help.path();
        if (path.startsWith("/")) {
            path = path.substring(1);
        }
        return HELP_BASE_URL + path;
    }

    /**
     * Resolves the documentation URL along the given node's parent chain (the URL-returning
     * variant of {@link #openHelp(Node)}); the fallback URL is returned when no annotated
     * ancestor is found.
     *
     * @param node the node to start the walk at, may be {@code null}
     * @param fallback the URL to return when nothing is annotated
     * @return the resolved documentation URL
     */
    public static String resolveContextHelpUrl(Node node, String fallback) {
        while (node != null) {
            String url = helpUrlOfClass(node.getClass());
            if (url != null) {
                return url;
            }
            node = node.getParent();
        }
        return fallback;
    }

    private static void openHelpInBrowser(String url) {
        LOGGER.info("Opening help in browser: {}", url);
        browserOpener.accept(url);
    }

    /**
     * Opens the given external URL in the default system browser via the application's host
     * services (Swing {@code SwingUtil.browse}, used by the About-menu browser actions
     * {@code KeYProjectHomepageAction} / {@code CreateGithubIssueAction} and by
     * {@code EditMostRecentFileAction}).
     * <p>
     * // menu: MP5 — opens the URL through the same {@linkplain #setBrowserOpener seam} as the
     * help pages (host services of the running application with a {@link Desktop} fallback), so
     * the self tests can record the target instead of launching a real browser.
     *
     * @param url the external URL to open
     */
    public static void openExternal(String url) {
        LOGGER.info("Opening external URL in browser: {}", url);
        browserOpener.accept(url);
    }

    /**
     * Replaces the browser-opening seam (self tests only).
     *
     * @param opener the new opener
     */
    static void setBrowserOpener(Consumer<String> opener) {
        browserOpener = opener;
    }

    /**
     * Self test of the help URL resolution logic (system property {@code key.fx.verify.help}),
     * run at startup from {@code MainWindowF}. Exercises the pure logic of the Swing original
     * without launching a browser: the seam records the URLs instead.
     *
     * @return a self-test report ending in {@code PASS} or {@code FAIL}
     */
    public static String verifyHelp() {
        StringBuilder report = new StringBuilder();
        Consumer<String> realOpener = browserOpener;
        try {
            // record instead of browsing
            String[] lastUrl = new String[1];
            browserOpener = url -> lastUrl[0] = url;

            // 1. default base URL and plain openHelp (HelpFacade.java:71-73)
            openHelp();
            check(report, "main page", HELP_BASE_URL, lastUrl[0]);

            // 2. relative path (HelpFacade.java:80-89)
            openHelp("user/ProofCaching/");
            check(report, "relative path", HELP_BASE_URL + "user/ProofCaching/", lastUrl[0]);

            // 3. leading slash is stripped
            openHelp("/user/Exploration/");
            check(report, "leading slash", HELP_BASE_URL + "user/Exploration/", lastUrl[0]);

            // 4. absolute https URL passes through unchanged
            openHelp("https://example.org/doc/");
            check(report, "absolute url", "https://example.org/doc/", lastUrl[0]);

            // 5. annotated class resolution (HelpFacade.java:117-124)
            lastUrl[0] = null;
            boolean found = openHelpOfClass(AnnotatedDummy.class);
            check(report, "annotated class", "true:" + HELP_BASE_URL + "/user/Annotated/",
                found + ":" + lastUrl[0]);

            // 6. unannotated class is rejected
            check(report, "unannotated class", "false",
                String.valueOf(openHelpOfClass(Dummy.class)));

            // 6b. the URL-returning resolution variants
            check(report, "helpUrlOfClass", HELP_BASE_URL + "user/Annotated/",
                helpUrlOfClass(AnnotatedDummy.class));
            check(report, "helpUrlOfClass unannotated", "null",
                String.valueOf(helpUrlOfClass(Dummy.class)));

            // 7. parent-chain resolution (HelpFacade.java:99-107): the annotated parent is
            // found from the child
            lastUrl[0] = null;
            Dummy child = new Dummy();
            AnnotatedDummy parent = new AnnotatedDummy();
            parent.getChildren().add(child);
            openHelp(child);
            check(report, "parent chain", HELP_BASE_URL + "/user/Annotated/", lastUrl[0]);
            check(report, "resolveContextHelpUrl parent", HELP_BASE_URL + "user/Annotated/",
                resolveContextHelpUrl(child, HELP_BASE_URL));

            // 8. a node without any annotated ancestor falls back to the main page (the FX
            // counterpart of the Swing OpenHelpAction behavior, see the class javadoc)
            lastUrl[0] = null;
            Dummy orphan = new Dummy();
            openHelp(orphan);
            check(report, "fallback", HELP_BASE_URL, lastUrl[0]);
            check(report, "resolveContextHelpUrl fallback", HELP_BASE_URL,
                resolveContextHelpUrl(orphan, HELP_BASE_URL));
        } catch (RuntimeException e) {
            report.append("exception ").append(e).append("; ");
        } finally {
            browserOpener = realOpener;
        }
        report.append(report.toString().contains("FAIL") || report.toString().contains("exception")
                ? "FAIL"
                : "PASS");
        return report.toString();
    }

    private static void check(StringBuilder report, String what, String expected,
            String actual) {
        boolean ok = java.util.Objects.equals(expected, actual);
        report.append(what).append("=").append(ok ? "ok"
                : "FAIL(expected <" + expected
                    + "> got <" + actual + ">)")
                .append("; ");
    }

    /** Unannotated node for the self test. */
    private static class Dummy extends javafx.scene.layout.VBox {
    }

    /** Annotated node for the self test. */
    @HelpInfoF(path = "/user/Annotated/")
    private static class AnnotatedDummy extends javafx.scene.layout.VBox {
    }
}
