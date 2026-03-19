/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

import java.awt.*;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.event.MouseWheelEvent;
import java.awt.event.MouseWheelListener;
import java.awt.geom.AffineTransform;
import java.awt.image.BufferedImage;
import javax.swing.*;

/**
 * A simple image view that may be panned and zoomed by the user.
 *
 * TODO: move to key.ui? it can be used for any image
 *
 * @author Arne Keller
 */
public class PanZoomImageView extends JComponent
        implements MouseListener, MouseMotionListener, MouseWheelListener {
    /**
     * Image to be displayed.
     */
    private final transient BufferedImage image;
    /**
     * Current display transformation.
     */
    private final AffineTransform at;
    /**
     * Timer used to control redraws.
     */
    private Timer timer;
    /**
     * Time of last paint in milliseconds.
     */
    private long lastPaint = 0;
    /**
     * Whether to render the image using a fast interpolation method.
     * Set to true when interacting with the image, set to false once the image is no longer moved.
     */
    private boolean quickRender = false;
    /**
     * Variable used to record mouse movements.
     *
     * @see #mouseDragged(MouseEvent)
     */
    private final Point p = new Point();

    /**
     * Construct a new image view for the given image and initial dimensions.
     * The component will react to resize events.
     *
     * @param img image to display
     * @param width width of the component
     * @param height height of the component
     */
    public PanZoomImageView(BufferedImage img, int width, int height) {
        this.image = img;

        int imageWidth = image.getWidth();
        int imageHeight = image.getHeight();
        double scale = 1.0;
        float scaleX = (float) width / imageWidth;
        float scaleY = (float) height / imageHeight;
        if (scaleX < 1.0 || scaleY < 1.0) {
            scale = Math.min(scaleX, scaleY);
        }
        double x = (width - scale * imageWidth) / 2;
        double y = (height - scale * imageHeight) / 2;
        at = AffineTransform.getScaleInstance(scale, scale);
        at.translate(x, y);

        this.timer = new Timer(150, e -> {
            if (quickRender && System.currentTimeMillis() - lastPaint > 100) {
                quickRender = false;
                repaint();
                this.timer.stop();
            }
        });
        addComponentListener(new ResizeListener());
        addMouseListener(this);
        addMouseMotionListener(this);
        addMouseWheelListener(this);
    }

    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);

        Graphics2D g2 = (Graphics2D) g;
        g2.setRenderingHint(RenderingHints.KEY_INTERPOLATION,
            quickRender ? RenderingHints.VALUE_INTERPOLATION_NEAREST_NEIGHBOR
                    : RenderingHints.VALUE_INTERPOLATION_BICUBIC);
        g2.drawRenderedImage(image, at);
    }

    @Override
    public void mouseClicked(MouseEvent e) {
    }

    @Override
    public void mousePressed(MouseEvent e) {
        p.setLocation(e.getPoint());
    }

    @Override
    public void mouseReleased(MouseEvent e) {
    }

    @Override
    public void mouseEntered(MouseEvent e) {
    }

    @Override
    public void mouseExited(MouseEvent e) {
    }

    @Override
    public void mouseDragged(MouseEvent e) {
        double deltaX = e.getX() - p.getX();
        double deltaY = e.getY() - p.getY();
        moveBy(deltaX, deltaY, e.getPoint());
    }

    @Override
    public void mouseMoved(MouseEvent e) {
    }

    @Override
    public void mouseWheelMoved(MouseWheelEvent e) {
        double scale = e.getWheelRotation() < 0 ? 1.1 : 0.9;
        this.scale(scale, -e.getX(), -e.getY());
    }

    private void scale(double scale, double dx, double dy) {
        AffineTransform mod = AffineTransform.getTranslateInstance(-dx, -dy);
        mod.scale(scale, scale);
        mod.translate(dx, dy);
        at.preConcatenate(mod);
        quickRender = true;
        RepaintManager.currentManager(this).markCompletelyDirty(this);
        lastPaint = System.currentTimeMillis();
        this.timer.start();
    }

    private void moveBy(double dx, double dy, Point point) {
        AffineTransform newAt = AffineTransform.getTranslateInstance(dx, dy);
        at.preConcatenate(newAt);
        p.setLocation(point);
        quickRender = true;
        RepaintManager.currentManager(this).markCompletelyDirty(this);
        lastPaint = System.currentTimeMillis();
        this.timer.start();
    }

    private static class ResizeListener extends ComponentAdapter {
        /**
         * Previously registered width of the component.
         */
        private double prevWidth = 0;
        /**
         * Previously registered height of the component.
         */
        private double prevHeight = 0;
        /**
         * Number of resize events observed.
         */
        private int events = 0;

        @Override
        public void componentResized(ComponentEvent e) {
            PanZoomImageView pziw = (PanZoomImageView) e.getComponent();
            double newWidth = e.getComponent().getWidth();
            double newHeight = e.getComponent().getHeight();
            events++;
            // System.out.println("event " + events + " " + e.paramString());
            // sometimes, the image view is "resized" when showing the window for the first time
            // => skip that event!
            if (events == 1 && newWidth < 300 && newHeight < 120) {
                events--;
                return;
            }
            if (events >= 2) {
                // rescale to fit the "smaller" of the two axes
                double ratio1 = newWidth / prevWidth;
                double ratio2 = newHeight / prevHeight;
                double ratio;
                if (ratio1 > 1.0 && ratio2 > 1.0) {
                    ratio = Math.min(ratio1, ratio2);
                } else {
                    ratio = Math.max(ratio1, ratio2);
                }
                pziw.moveBy((newWidth - prevWidth) / 2.0, (newHeight - prevHeight) / 2.0, pziw.p);
                pziw.scale(ratio, -newWidth / 2.0, -newHeight / 2.0);
            }
            prevWidth = newWidth;
            prevHeight = newHeight;
        }
    }
}
