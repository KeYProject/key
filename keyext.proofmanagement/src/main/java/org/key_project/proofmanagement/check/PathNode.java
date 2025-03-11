/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check;

import java.nio.file.Files;
import java.nio.file.Path;

/**
 * Represents a node in a file tree where nodes contain Path objects.
 *
 * @author Wolfram Pfeifer
 */
public class PathNode extends Node<Path> {

    /**
     * Creates a new PathNode with given parent and content.
     *
     * @param parent the parent of the new node
     * @param element the Path to store at the new PathNode
     */
    public PathNode(PathNode parent, Path element) {
        super(parent, element);
    }

    @Override
    public PathNode getParent() {
        return (PathNode) super.getParent();
    }

    @Override
    public String toString() {
        return getContent().getFileName().toString();
    }

    @Override
    public int compareTo(Node<Path> o) {
        Path myPath = getContent();
        Path otherPath = o.getContent();

        // directories first!
        if (Files.isDirectory(myPath) && !Files.isDirectory(otherPath)) {
            return -1;
        } else if (!Files.isDirectory(myPath) && Files.isDirectory(otherPath)) {
            return 1;
        }
        // both paths denote files or both denote directories
        return myPath.compareTo(otherPath);
    }
}
