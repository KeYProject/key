/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.lookup;

import java.util.*;

/// Implements a mutable trie structure for storing and retrieving values
/// associated with a key sequence (word). Valid key sequences have to be
/// prefix codes, i.e., no sequence is a prefix of a different one.
///
/// Values are only stored in leaves and a leaf must store a value.
/// The latter has also consequences for removal operations: if
/// a leaf stores no values after the remove operation, the leaf itself
/// is removed as a child of its parent. If the parent itself has
/// no other children it will also be removed. This continues until an
/// ancestor is reached with more than one child.
///
/// @param <K> the element type of key sequence
/// @param <V> the type of the values stored in the trie
public class Trie<K, V> {

    private TrieNode<K, V> root;

    /// Associates the provided value with given key sequence
    /// It returns true if the value had not been already
    /// inserted, otherwise the trie remains unchanged and false
    /// is returned.
    /// @param word key sequence to be associated with the value
    /// @param value to be associated
    /// @return true iff the value has been associated and no
    /// association existed before
    /// @throws NullPointerException if a prefix code violation occurred
    public boolean insert(Iterator<K> word, V value) {
        if (!word.hasNext()) {
            return false;
        }
        if (root == null) {
            root = new TrieNode<>(true);
        }
        return root.insert(word, value);
    }

    /// Retrieves the values associated with the given key sequence.
    /// If no values are associated with the provided key sequence
    /// an empty set is returned
    /// @param word key sequence to be associated with the value
    /// @return set of values associated with key sequence
    /// @throws NullPointerException if a prefix code violation occurred
    public Set<V> lookup(Iterator<K> word) {
        return root == null ? Collections.emptySet() : root.lookup(word);
    }

    /// removes all values associated with the key-sequence
    /// @param word key sequence whose associated values are removed
    /// @return true iff the key sequence had associated values which were successfully removed
    public boolean removeAll(Iterator<K> word) {
        return root != null && root.removeAll(word);
    }

    /// removes the provided values from the set of values associated with the key-sequence
    /// @param word the key sequence
    /// @param value the value to be removed
    /// @return values associated with the key sequence after removal (may save and additional
    /// lookup)
    public Set<V> remove(Iterator<K> word, V value) {
        return root == null ? Collections.emptySet() : root.remove(word, value);
    }

    /// removes all assocation below the provided fragment of a key sequence.
    /// This means the key sequence may not be a prefix code, but instead specify
    /// the values of the key sequences being continuation of this fragment to be
    /// deleted
    /// @param fragment fragment of a key sequence
    /// @return true iff key sequences being continuation of the provided fragment
    /// were managed by the trie and whose associated values are now removed
    public boolean removeSubtrie(Iterator<K> fragment) {
        if (fragment.hasNext()) {
            if (root == null) {
                return false;
            }
            boolean result = root.removeSubtrie(fragment);
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

        private TrieNode() {
        }

        /// creates a new inner node or a leaf node. An inner node has children,
        /// but no values and vice versa.
        /// @param inInner true if an inner node should be created, false for leaves
        public TrieNode(boolean inInner) {
            if (inInner) {
                children = new HashMap<>();
            } else {
                values = new HashSet<>();
            }
        }

        /// see {@link Trie#insert(Iterator, Object)}
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

        /// see {@link Trie#lookup(Iterator)}
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

        /// see {@link Trie#removeAll(Iterator)}
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

        /// see {@link Trie#remove(Iterator, Object)}
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

        /// see {@link Trie#removeSubtrie(Iterator)}
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

        /// utility method to remove left-overs after removal of parts of the tree.
        /// This means parts of branches ending with a node that has neither values nor children
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

        /// helper record to manage pairs
        private record Pair<K, V>(K key, TrieNode<K, V> child) {
        }
    }
}
