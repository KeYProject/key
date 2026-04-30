/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.lookup;

import java.util.*;

/**
 * Implements a mutable trie structure for storing and retrieving values
 * associated with a sequence of keys (word). The sequence has to be
 * prefix unique, i.e., no sequence is a prefix of a different one.
 *
 * Values are only stored in leaves and a leaf must store a value.
 * The latter has also consequences for removal operations: if
 * a leaf stores no values after the remove operation, the leaf itself
 * is removed as a child of its parent. If the parent itself has
 * no other children it will also be removed. This continues until an
 * ancestor is reached with more than one child.
 *
 *
 * @param <K> the type of the key objects
 * @param <V> the type of the values stored in the trie
 */
public class Trie<K, V> {

    private TrieNode<K, V> root;

    public Trie() {
    }

    private boolean insert(Iterator<K> word, V value) {
        if (!word.hasNext()) {
            return false;
        }
        if (root == null) {
            root = new TrieNode<>(true);
        }
        return root.insert(word, value);
    }

    private Set<V> lookup(Iterator<K> word) {
        return root == null ? Collections.emptySet() : root.lookup(word);
    }

    private boolean removeAll(Iterator<K> word) {
        return root != null && root.removeAll(word);
    }

    private Set<V> remove(Iterator<K> word, V value) {
        return root == null ? Collections.emptySet() : root.remove(word, value);
    }

    private boolean removeSubtrie(Iterator<K> word) {
        if (word.hasNext()) {
            if (root == null) {
                return false;
            }
            boolean result = root.removeSubtrie(word);
            if (result) {
                if (root.children == null || root.children.isEmpty()) {
                    root = null;
                }
                return true;
            } else {
                return false;
            }
        }
        root = null;
        return true;
    }

    private static class TrieNode<K, V> {

        private Map<K, TrieNode<K, V>> children;
        private Set<V> values;

        private TrieNode() {}

        public TrieNode(boolean inInner) {
            if (inInner) {
                children = new HashMap<>();
            } else {
                values = new HashSet<>();
            }
        }

        boolean insert(Iterator<K> word, V value) {
            TrieNode<K, V> current = this;
            while (word.hasNext()) {
                K key = word.next();
                if (current.children.containsKey(key)) {
                    current = current.children.get(key);
                } else {
                    TrieNode<K, V> child = new TrieNode<>(word.hasNext());
                    current.children.put(key, child);
                    current = child;
                }
            }
            return current.values.add(value);
        }

        Set<V> lookup(Iterator<K> word) {
            TrieNode<K, V> current = this;
            while (word.hasNext()) {
                K key = word.next();
                if (current.children.containsKey(key)) {
                    current = current.children.get(key);
                } else {
                    return Collections.emptySet();
                }
            }
            return new HashSet<>(current.values);
        }

        boolean removeAll(Iterator<K> word) {
            Stack<Pair<K, V>> path = new Stack<>();
            TrieNode<K, V> current = this;
            while (word.hasNext()) {
                K key = word.next();
                if (current.children.containsKey(key)) {
                    current = current.children.get(key);
                    path.push(new Pair<>(key, current));
                } else {
                    return false;
                }
            }
            current.values = null;
            trimTrie(path, current);
            return true;
        }

        Set<V> remove(Iterator<K> word, V value) {
            Stack<Pair<K, V>> path = new Stack<>();
            TrieNode<K, V> current = this;
            while (word.hasNext()) {
                K key = word.next();
                if (current.children.containsKey(key)) {
                    current = current.children.get(key);
                    path.push(new Pair<>(key, current));
                } else {
                    return Collections.emptySet();
                }
            }
            current.values.remove(value);
            Set<V> currentValues = new HashSet<>(current.values);
            if (currentValues.isEmpty()) {
                trimTrie(path, current);
            }
            return currentValues;
        }

        boolean removeSubtrie(Iterator<K> word) {
            Stack<Pair<K, V>> path = new Stack<>();
            TrieNode<K, V> current = this;
            while (word.hasNext()) {
                K key = word.next();
                if (current.children.containsKey(key)) {
                    current = current.children.get(key);
                    path.push(new Pair<>(key, current));
                } else {
                    return false;
                }
            }
            current.values = null;
            current.children = null;
            trimTrie(path, current);
            return true;
        }

        private void trimTrie(Stack<Pair<K, V>> path, TrieNode<K, V> current) {
            while (!path.isEmpty()) {
                Pair<K, V> prev = path.pop();
                current.children.remove(prev.key);
                current = prev.child;
                if (!current.children.isEmpty()) {
                    break;
                } else {
                    current.children = null;
                }
            }
        }

        private record Pair<K, V>(K key, TrieNode<K, V> child) {
        }
    }
}

