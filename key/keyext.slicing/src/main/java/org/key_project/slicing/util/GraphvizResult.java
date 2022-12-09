package org.key_project.slicing.util;

import java.awt.image.BufferedImage;

/**
 * Either an image or an error.
 *
 * @author Arne Keller
 */
public class GraphvizResult {
    private final BufferedImage image;
    private final String error;

    private GraphvizResult(BufferedImage image, String error) {
        this.image = image;
        this.error = error;
    }

    public static GraphvizResult makeImage(BufferedImage image) {
        return new GraphvizResult(image, null);
    }

    public static GraphvizResult makeError(String error) {
        return new GraphvizResult(null, error);
    }

    public boolean hasImage() {
        return image != null;
    }

    public BufferedImage getImage() {
        return image;
    }

    public boolean hasError() {
        return error != null;
    }

    public String getError() {
        return error;
    }
}
