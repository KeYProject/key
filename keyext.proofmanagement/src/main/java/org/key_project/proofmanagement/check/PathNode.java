/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.proofmanagement.check;

import java.nio.file.Files;
import java.nio.file.Path;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a node in a file tree where nodes contain Path objects.
 *
 * @author Wolfram Pfeifer
 */
@NullMarked
public class PathNode extends Node<Path> {

    /**
     * Creates a new PathNode with given parent and content.
     *
     * @param parent the parent of the new node
     * @param element the Path to store at the new PathNode
     */
    public PathNode(@Nullable PathNode parent, Path element) {
        super(parent, element);
    }

    @Override
    public @Nullable PathNode getParent() {
        return (PathNode) super.getParent();
    }

    @Override
    public String toString() {
        Path fileName = getContent().getFileName();
        if (fileName == null) {
            throw new NullPointerException("Path has no file name: " + getContent());
        }
        return fileName.toString();
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
