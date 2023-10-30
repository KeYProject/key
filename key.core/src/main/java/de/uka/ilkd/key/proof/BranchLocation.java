/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Describes a branch in a proof as a series of branch choices.
 * Each branch choice is a proof node and the sub-node to descend into.
 *
 * @author Arne Keller
 */
public class BranchLocation {
    /**
     * Branch location of the initial proof branch.
     */
    public static final BranchLocation ROOT = new BranchLocation(ImmutableSLList.nil());

    /**
     * List of branch choices (branching nodes and sub-proof indices).
     */
    private final ImmutableList<Pair<Node, Integer>> location;

    /**
     * Construct a new branch location given a list of branch choices.
     *
     * @param location series of branch choices
     */
    public BranchLocation(ImmutableList<Pair<Node, Integer>> location) {
        this.location = location;
    }

    /**
     * Compute the (longest) common prefix of a set of branch locations.
     *
     * @param locations branch locations
     * @return their common prefix
     */
    public static BranchLocation commonPrefix(BranchLocation... locations) {
        if (locations.length == 0) {
            throw new IllegalArgumentException(
                "can't determine common prefix of 0 branch locations");
        }
        BranchLocation prefix = BranchLocation.ROOT;
        int i = 0;
        boolean keepGoing = true;
        while (keepGoing) {
            for (BranchLocation branchLocation : locations) {
                if (branchLocation.size() <= i) {
                    keepGoing = false;
                    break;
                }
            }
            if (!keepGoing) {
                break;
            }
            Pair<Node, Integer> x = locations[0].get(i);
            for (int j = 1; j < locations.length; j++) {
                if (!locations[j].get(i).equals(x)) {
                    keepGoing = false;
                    break;
                }
            }
            if (keepGoing) {
                prefix = prefix.append(locations[0].get(i));
                i++;
            }
        }
        return prefix;
    }

    /**
     * Remove a prefix from this branch location.
     *
     * @param prefix prefix to remove
     * @return the remaining suffix
     */
    public BranchLocation stripPrefix(BranchLocation prefix) {
        return new BranchLocation(location.stripPrefix(prefix.location));
    }

    /**
     * Add a branch choice to this branch location.
     *
     * @param newBranch branch choice
     * @return extnded branch location
     */
    public BranchLocation append(Pair<Node, Integer> newBranch) {
        return new BranchLocation(location.append(newBranch));
    }

    /**
     * Remove the last branch choice.
     *
     * @return shorter branch location
     */
    public BranchLocation removeLast() {
        List<Pair<Node, Integer>> list = location.toList();
        list.remove(list.size() - 1);
        return new BranchLocation(ImmutableList.fromList(list));
    }

    /**
     * @return the length of this branch location
     */
    public int size() {
        return location.size();
    }

    /**
     * @return whether this branch location is the initial proof branch
     */
    public boolean isEmpty() {
        return location.isEmpty();
    }

    private Pair<Node, Integer> get(int idx) {
        return location.stream().skip(idx).findFirst().get();
    }

    /**
     * Get the branching proof node of the branch choice at the specified index.
     *
     * @param idx index
     * @return branching proof node
     */
    public Node getNode(int idx) {
        return get(idx).first;
    }

    /**
     * @param prefix other branch location
     * @return whether this branch location is built on the provided location
     */
    public boolean hasPrefix(BranchLocation prefix) {
        return location.hasPrefix(prefix.location);
    }

    @Override
    public String toString() {
        var id = new StringBuilder();
        location.stream()
                .forEachOrdered(it -> id
                        .append('/')
                        .append(it.first.serialNr())
                        .append('_')
                        .append(it.second));
        return id.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        BranchLocation that = (BranchLocation) o;
        return Objects.equals(location, that.location);
    }

    @Override
    public int hashCode() {
        return Objects.hash(location);
    }
}
