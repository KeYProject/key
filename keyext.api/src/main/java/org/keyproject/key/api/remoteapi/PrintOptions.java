package org.keyproject.key.api.remoteapi;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public record PrintOptions(boolean unicode, int width, int indentation, boolean pure,
                           boolean termLabels) {
}
