package de.uka.ilkd.key.loopinvgen;

import java.util.*;

class Graph<T> {
    // Maps locSet to dependence predicates
    private Map<T, List<T> > map = new HashMap<>();
    public void addVertex(T s)
    {
        map.put(s, new LinkedList<T>());
    }

    public void addEdge(T source,
                        T destination,
                        boolean bidirectional)
    {

        if (!map.containsKey(source))
            addVertex(source);

        if (!map.containsKey(destination))
            addVertex(destination);

        map.get(source).add(destination);
        if (bidirectional == true) {
            map.get(destination).add(source);
        }
    }

    public void getVertexCount()
    {
        System.out.println("The graph has "
                + map.keySet().size()
                + " vertex");
    }

    // This function gives the count of edges
    public void getEdgesCount(boolean bidirection)
    {
        int count = 0;
        for (T v : map.keySet()) {
            count += map.get(v).size();
        }
        if (bidirection == true) {
            count = count / 2;
        }
        System.out.println("The graph has "
                + count
                + " edges.");
    }

    // This function gives whether
    // a vertex is present or not.
    public boolean hasVertex(T s)
    {
        if (map.containsKey(s)) {
//            System.out.println("The graph contains "
//                    + s + " as a vertex.");
            return true;
        }
        else {
//            System.out.println("The graph does not contain "
//                    + s + " as a vertex.");
        }
        return false;
    }

    // This function gives whether an edge is present or not.
    public boolean hasEdge(T s, T d)
    {
        if (map.get(s).contains(d)) {
//            System.out.println("The graph has an edge between "
//                    + s + " and " + d + ".");
            return  true;
        }
        else {
//            System.out.println("The graph has no edge between "
//                    + s + " and " + d + ".");
        }
        return false;
    }

    // Prints the adjancency list of each vertex.
    @Override
    public String toString()
    {
        StringBuilder builder = new StringBuilder();

        for (T v : map.keySet()) {
            builder.append(v.toString() + ": ");
            for (T w : map.get(v)) {
                builder.append(w.toString() + " ");
            }
            builder.append("\n");
        }

        return (builder.toString());
    }
}