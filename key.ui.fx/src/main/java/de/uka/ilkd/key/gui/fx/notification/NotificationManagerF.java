/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

import javafx.animation.FadeTransition;
import javafx.animation.PauseTransition;
import javafx.application.Platform;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.geometry.Pos;
import javafx.scene.control.Label;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;
import javafx.scene.layout.VBox;
import javafx.util.Duration;

/**
 * Shows transient toast notifications in the top-right corner of the main window.
 * <p>
 * Counter-part of the {@code NotificationManager} of the Swing module {@code key.ui}. Notifications
 * are plain JavaFX labels with the {@code notification-toast} style class (see
 * {@code key-light.css}/{@code key-dark.css}); they auto-dismiss after a configurable timeout and
 * dismiss immediately when clicked.
 */
public final class NotificationManagerF {

    /** Severity of a notification, mapped to a CSS style class. */
    public enum Kind {
        INFO("info"),
        WARNING("warning"),
        ERROR("error");

        private final String styleClass;

        Kind(String styleClass) {
            this.styleClass = styleClass;
        }

        String styleClass() {
            return styleClass;
        }
    }

    private static final NotificationManagerF INSTANCE = new NotificationManagerF();

    private final VBox toastBox = new VBox(6);
    private final SimpleObjectProperty<Duration> timeout =
        new SimpleObjectProperty<>(this, "timeout", Duration.seconds(5));

    private NotificationManagerF() {
        toastBox.setPickOnBounds(false);
        toastBox.getStyleClass().add("notification-overlay");
        // prevent the stack pane from stretching the box to the full width, which would push
        // the toasts to the left edge
        toastBox.setMaxWidth(420);
        toastBox.setAlignment(Pos.TOP_RIGHT);
    }

    /**
     * @return the global notification manager instance
     */
    public static NotificationManagerF getInstance() {
        return INSTANCE;
    }

    /**
     * Attaches the toast overlay to the given pane, which should cover the content area of the
     * main window. The overlay is mouse-transparent outside of the toasts themselves, so normal
     * interaction with the content below is unaffected.
     *
     * @param overlay the pane to place the toasts in
     */
    public void attach(Pane overlay) {
        if (!overlay.getChildren().contains(toastBox)) {
            overlay.getChildren().add(toastBox);
            StackPane.setAlignment(toastBox, Pos.TOP_RIGHT);
            toastBox.setTranslateX(-12);
            toastBox.setTranslateY(40);
        }
    }

    /**
     * @return the auto-dismiss timeout of toasts
     */
    public ObjectProperty<Duration> timeoutProperty() {
        return timeout;
    }

    /**
     * Shows an informational notification.
     *
     * @param message the message to display
     */
    public void notify(String message) {
        notify(message, Kind.INFO);
    }

    /**
     * Shows a notification with the given severity.
     *
     * @param message the message to display
     * @param kind the severity
     */
    public void notify(String message, Kind kind) {
        Platform.runLater(() -> {
            Label toast = new Label(message);
            toast.getStyleClass().addAll("notification-toast", kind.styleClass());
            toast.setMaxWidth(420);
            toast.setWrapText(true);
            toast.setOnMouseClicked(ignored -> dismiss(toast));

            toastBox.getChildren().add(toast);
            PauseTransition pause = new PauseTransition(timeout.get());
            pause.setOnFinished(ignored -> dismiss(toast));
            pause.play();
        });
    }

    private void dismiss(Label toast) {
        if (toastBox.getChildren().contains(toast)) {
            FadeTransition fade = new FadeTransition(Duration.millis(200), toast);
            fade.setOnFinished(
                ignored -> Platform.runLater(() -> toastBox.getChildren().remove(toast)));
            fade.play();
        }
    }

    /**
     * @return the number of currently visible toasts (self-test hook used by the
     *         {@code key.fx.verify.notifications} verification)
     */
    public int getVisibleToastCount() {
        return toastBox.getChildren().size();
    }
}
