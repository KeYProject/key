/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import javafx.animation.KeyFrame;
import javafx.animation.Timeline;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;
import javafx.stage.StageStyle;
import javafx.stage.Window;
import javafx.util.Duration;

/**
 * Tiny timed popup — the port of the Swing {@code de.uka.ilkd.key.gui.AutoDismissDialog}
 * (key.ui, 104 lines). It is shown when the "Stop on non-closeable goal" mode could not close a
 * goal automatically (Swing trigger: {@code WindowUserInterfaceControl.java:202-205} and
 * {@code :227-229}) and disposes itself after a delay with a color-fade countdown.
 * <p>
 * Ported behaviors (Swing evidence): the pink message panel ({@code AutoDismissDialog.java:40},
 * color {@code (1, 0.7f, 0.7f)}), a timer disposes the dialog after {@link #DEFAULT_DELAY} ms
 * ({@code :64-71}) and a periodic task fades the panel color from pink towards white over
 * {@code steps = (delay - delayStartToDispose - delayDisposeToEnd) / rate} steps starting at
 * {@link #DEFAULT_DELAY_START_TO_DISPOSE} ({@code :72-83}). Small documented addition: the
 * dialog also dismisses on click (the Swing original stays until the timer fires; the FX toast
 * convention established by {@code NotificationManagerF} made the click affordance consistent).
 */
public class AutoDismissDialogF {
    public static final int DEFAULT_DELAY = 5000;
    public static final int DEFAULT_RATE = 25;
    public static final int DEFAULT_DELAY_START_TO_DISPOSE = 2000;
    public static final int DEFAULT_DELAY_DISPOSE_TO_END = 1000;

    private final Stage stage = new Stage(StageStyle.UTILITY);
    private final VBox messagePanel = new VBox();
    private final int delay, rate, delayStartToDispose;
    private final int steps;

    /**
     * Creates an auto-dismiss dialog with the given timing parameters (Swing
     * {@code AutoDismissDialog.java:35-49}).
     *
     * @param owner owner window (the dialog is centered on it), may be null
     * @param message the message to show
     * @param delay the total delay until the dialog disposes itself (ms)
     * @param rate the period of the color fade task (ms)
     * @param delayStartToDispose the delay before the fade starts (ms)
     * @param delayDisposeToEnd kept for Swing parameter parity (unused in the fade math of the
     *        Swing original besides the step computation)
     */
    public AutoDismissDialogF(Window owner, String message, final int delay, final int rate,
            final int delayStartToDispose, final int delayDisposeToEnd) {
        this.delay = delay;
        this.rate = rate;
        this.delayStartToDispose = delayStartToDispose;
        steps = (delay - delayStartToDispose - delayDisposeToEnd) / rate;

        Label label = new Label(message);
        label.setWrapText(true);
        messagePanel.getChildren().add(label);
        messagePanel.getStyleClass().add("auto-dismiss-dialog");
        messagePanel.setPadding(new Insets(10, 16, 10, 16));
        messagePanel.setOnMouseClicked(e -> stage.close());

        Scene scene = new Scene(messagePanel);
        de.uka.ilkd.key.gui.fx.theme.ThemeManager.getInstance().manage(scene);
        stage.setScene(scene);
        stage.setTitle("Message");
        stage.setAlwaysOnTop(true);
        if (owner != null) {
            centerOn(owner);
        }
    }

    /**
     * Creates an auto-dismiss dialog with the Swing default timing (Swing
     * {@code AutoDismissDialog.java:52-55}).
     *
     * @param owner owner window, may be null
     * @param message the message to show
     */
    public AutoDismissDialogF(Window owner, String message) {
        this(owner, message, DEFAULT_DELAY, DEFAULT_RATE, DEFAULT_DELAY_START_TO_DISPOSE,
            DEFAULT_DELAY_DISPOSE_TO_END);
    }

    /**
     * Creates an owner-less auto-dismiss dialog (Swing {@code AutoDismissDialog.java:58-60}).
     *
     * @param message the message to show
     */
    public AutoDismissDialogF(String message) {
        this(null, message);
    }

    private void centerOn(Window owner) {
        stage.sizeToScene();
        stage.setX(owner.getX() + owner.getWidth() / 2 - stage.getWidth() / 2);
        stage.setY(owner.getY() + owner.getHeight() / 2 - stage.getHeight() / 2);
    }

    /**
     * Shows the dialog and starts the timer tasks (Swing {@code AutoDismissDialog.show},
     * {@code :63-85}): the color fade from pink towards white and the dispose after
     * {@code delay} ms. Must be called on the FX Application Thread.
     */
    public void show() {
        Timeline fade = new Timeline(new KeyFrame(Duration.millis(rate), e -> fade()));
        fade.setCycleCount(steps);
        fade.setDelay(Duration.millis(delayStartToDispose));
        fade.play();

        Timeline dispose = new Timeline(new KeyFrame(Duration.millis(delay), e -> stage.close()));
        dispose.play();
        stage.show();
    }

    /** One fade step (Swing {@code :75-82}): the red channel stays 1, green/blue rise. */
    private void fade() {
        int remaining = Math.max(0, steps - ++fadeTicks);
        double alpha = (double) remaining / (double) steps;
        double rgValue = 0.7 + 0.3 * (1 - alpha);
        messagePanel.setStyle("-fx-background-color: rgba(255, " + to255(rgValue) + ", "
            + to255(rgValue) + ", 1.0);");
    }

    private int fadeTicks;

    private static int to255(double value) {
        return (int) Math.round(Math.clamp(value, 0.0, 1.0) * 255);
    }

    /** @return the underlying stage (for tests) */
    public Stage getStage() {
        return stage;
    }

    /** @return whether the popup is currently shown (self-test hook) */
    public boolean isVisible() {
        return stage.isShowing();
    }
}
