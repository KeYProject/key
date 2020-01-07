package org.key_project.proofmanagement.check;

import java.nio.file.Files;
import java.nio.file.Path;

public class PathNode extends Node<Path> {

    public PathNode(PathNode parent, Path element) {
        super(parent, element);
    }

    @Override
    public PathNode getParent() {
        return (PathNode) super.getParent();
    }

    @Override
    public String toString() {
        return content.getFileName().toString();
    }

    @Override
    public int compareTo(Node<Path> o) {
        Path myPath = content;
        Path otherPath = o.content;

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
