package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.Objects;

public class BranchLocation {
    /**
     * List of branching nodes and sub-proof indices.
     */
    private final ImmutableList<Pair<Node, Integer>> location;

    public static BranchLocation root() {
        return new BranchLocation(ImmutableSLList.nil());
    }

    public BranchLocation(ImmutableList<Pair<Node, Integer>> location) {
        this.location = location;
    }

    public static BranchLocation commonPrefix(BranchLocation... locations) {
        if (locations.length == 0) {
            throw new IllegalArgumentException(
                    "can't determine common prefix of 0 branch locations");
        }
        var prefix = BranchLocation.root();
        var i = 0;
        var keepGoing = true;
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
            var x = locations[0].get(i);
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

    public BranchLocation stripPrefix(BranchLocation prefix) {
        return new BranchLocation(location.stripPrefix(prefix.location));
    }

    public BranchLocation append(Pair<Node, Integer> newBranch) {
        return new BranchLocation(location.append(newBranch));
    }

    public BranchLocation removeLast() {
        var list = location.toList();
        list.remove(list.size() - 1);
        return new BranchLocation(ImmutableList.fromList(list));
    }

    public int size() {
        return location.size();
    }

    public boolean isEmpty() {
        return location.isEmpty();
    }

    private Pair<Node, Integer> get(int idx) {
        return location.stream().skip(idx).findFirst().get();
    }

    public Node getNode(int idx) {
        return get(idx).first;
    }

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
