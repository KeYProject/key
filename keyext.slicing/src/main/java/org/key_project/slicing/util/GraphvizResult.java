/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.util;

import java.awt.image.BufferedImage;

/**
 * Result of running an external graph renderer.
 * Either an image or an error.
 *
 * @param image The image.
 * @param error The error message.
 * @author Arne Keller
 */
public record GraphvizResult(BufferedImage image, String error) {
    public GraphvizResult {
        if ((image != null) == (error != null)) {
            throw new IllegalArgumentException("result must either be an image or an error");
        }
    }

    /**
     * @param image rendered image
     * @return new result object with that image attached
     */
    public static GraphvizResult makeImage(BufferedImage image) {
        return new GraphvizResult(image, null);
    }

    /**
     * @param error error text
     * @return new result object with that error attached
     */
    public static GraphvizResult makeError(String error) {
        return new GraphvizResult(null, error);
    }

    /**
     * @return whether this result has an image
     */
    public boolean hasImage() { return image != null; }

    /**
     * @return the rendered image (null if error is present)
     */
    @Override
    public BufferedImage image() { return image; }

    /**
     * @return whether this result indicates an error
     */
    public boolean hasError() { return error != null; }

    /**
     * @return the error message (null if image was rendered)
     */
    @Override
    public String error() { return error; }
}
