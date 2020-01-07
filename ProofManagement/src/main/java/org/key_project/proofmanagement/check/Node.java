package org.key_project.proofmanagement.check;

import org.jetbrains.annotations.NotNull;

import java.util.*;

public class Node<T extends Comparable<T>> implements Comparable<Node<T>> {
    public final Node<T> parent;
    public final SortedSet<Node<T>> children = new TreeSet<>();
    public final T content;

    public Node(Node<T> parent, T element) {
        this.parent = parent;
        this.content = element;
    }

    public Node<T> getParent() {
        return parent;
    }

    public boolean isDirectory() {
        return !children.isEmpty();
    }

    public SortedSet<Node<T>> getChildren() {
        return children;
    }

    public void addChild(Node<T> child) {
        children.add(child);
    }

    @Override
    public int compareTo(@NotNull Node<T> o) {
        return content.compareTo(o.content);
    }
}
