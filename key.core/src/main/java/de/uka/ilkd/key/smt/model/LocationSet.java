/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.model;

import java.util.LinkedList;
import java.util.List;

/**
 * A LocationSet represents a location set in an SMT model.
 *
 * @author mihai
 *
 */

public class LocationSet {
    /**
     * The name of the location set.
     */
    private String name;
    /**
     * The locations contained in the location set.
     */
    private List<Location> locations;

    public LocationSet(String name) {
        this.name = name;
        locations = new LinkedList<>();
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public int size() {
        return locations.size();
    }



    public List<Location> getLocations() {
        return locations;
    }

    public void setLocations(List<Location> locations) {
        this.locations = locations;
    }

    public boolean add(Location e) {
        return locations.add(e);
    }

    public Location get(int index) {
        return locations.get(index);
    }

    public String toString() {

        StringBuilder result = new StringBuilder(name);

        result.append(" = {");

        for (Location ls : locations) {
            result.append(ls);
            result.append(", ");
        }

        result = new StringBuilder(result.toString().trim());
        if (result.toString().contains(",")) {
            result = new StringBuilder(result.substring(0, result.toString().lastIndexOf(',')));
        }
        result.append("}");


        return result.toString();
    }

    /**
     * Location sets with equal names are equal.
     */
    public boolean equals(Object o) {

        if (o instanceof LocationSet) {

            LocationSet ls = (LocationSet) o;
            return ls.name.equals(name);


        }

        return false;


    }



}
