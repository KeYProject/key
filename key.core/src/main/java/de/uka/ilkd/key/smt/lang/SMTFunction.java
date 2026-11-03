/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.smt.lang;

import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 *
 *
 * @author Aboubakr Achraf El Ghazi
 *
 */
@NullMarked
public class SMTFunction {

    protected @Nullable String comment;

    public @Nullable String getComment() {
        return comment;
    }

    public void setComment(@Nullable String comment) {
        this.comment = comment;
    }

    protected @Nullable String id;
    protected @Nullable List<SMTSort> domainSorts;
    protected @Nullable SMTSort imageSort;

    /**
     * creates an inital SMT function
     */
    public SMTFunction() {
        super();
        this.id = null;
        this.domainSorts = null;
        this.imageSort = null;
    }

    public SMTFunction(String id, List<SMTSort> domainSorts, SMTSort imageSort) {
        super();
        this.id = Util.processName(id);
        this.domainSorts = domainSorts;
        this.imageSort = imageSort;
    }

    public SMTFunction(String id, SMTSort argSort1, SMTSort argSort2, SMTSort imageSort) {
        super();
        this.id = Util.processName(id);
        List<SMTSort> domainSorts = new LinkedList<>();
        domainSorts.add(argSort1);
        domainSorts.add(argSort2);
        this.domainSorts = domainSorts;
        this.imageSort = imageSort;
    }

    public @Nullable SMTSort getImageSort() {
        return imageSort;
    }

    public void setImageSort(@Nullable SMTSort imageSort) {
        this.imageSort = imageSort;
    }

    public @Nullable String getId() {
        return id;
    }

    public void setId(@Nullable String id) {
        this.id = id;
    }

    public String processString(String id) {
        // is symbol already quoted?
        if (id.startsWith("|") && id.endsWith("|")) {
            return id;
        }

        id = id.replace("::", ".");
        id = id.replace("<", "");
        id = id.replace(">", "");
        id = id.replace("$", "");
        id = id.replace("store", "store_");


        // do i need to quote symbol?
        boolean quote = id.contains(":") || id.contains("[") || id.contains("]") || id.contains("(")
                || id.contains(")");

        if (quote) {
            return "|" + id + "|";
        } else {
            return id;
        }
    }



    /**
     * @return the domainSorts
     */
    public @Nullable List<SMTSort> getDomainSorts() {
        return domainSorts;
    }

    /**
     * @param domainSorts the domainSorts to set
     */
    public void setDomainSorts(@Nullable List<SMTSort> domainSorts) {
        this.domainSorts = domainSorts;
    }

    @Override
    public boolean equals(@Nullable Object obj) {
        if (obj == null) {
            return false;
        }

        if (this == obj) {
            return true;
        }

        if (!(obj instanceof SMTFunction f)) {
            return false;
        }

        final String thisId = Objects.requireNonNull(this.id, "id");
        final List<SMTSort> thisDomainSorts =
            Objects.requireNonNull(this.domainSorts, "domainSorts");
        final List<SMTSort> otherDomainSorts =
            Objects.requireNonNull(f.domainSorts, "domainSorts");

        if (!thisId.equals(f.id)) {
            return false;
        }

        if (thisDomainSorts.size() != otherDomainSorts.size()) {
            return false;
        }

        for (int i = 0; i < thisDomainSorts.size(); i++) {
            if (!thisDomainSorts.get(i).equals(otherDomainSorts.get(i))) {
                return false;
            }
        }
        return true;
    }

    // public boolean equals (Function f) {
    // if (f == null)
    // return false;
    //
    // if (f == this)
    // return true;
    //
    // if (!this.id.equals(f.id))
    // return false;
    //
    // if (this.domainSorts.size() != f.domainSorts.size())
    // return false;
    //
    // for (int i = 0; i < this.domainSorts.size(); i++) {
    // if (!this.domainSorts.get(i).equals(f.domainSorts.get(i)))
    // return false;
    // }
    // return true;
    // }

    @Override
    public int hashCode() {
        int ret = Objects.requireNonNull(id, "id").hashCode();
        int base = 10;
        int i = 1;

        for (SMTSort sort : Objects.requireNonNull(domainSorts, "domainSorts")) {
            ret = ret + sort.getId().hashCode() * base ^ i;
            i++;
        }

        return ret;
    }

    public String toString() {
        StringBuilder buff = new StringBuilder();

        buff.append("(declare-fun ").append(id).append(" ").append("(");
        // if (domainSorts == null) return "domainSorts is null";
        for (SMTSort s : Objects.requireNonNull(domainSorts, "domainSorts")) {
            buff.append(s.getTopLevel().getId()).append(" ");
        }
        buff.append(")" + " ").append(Objects.requireNonNull(imageSort, "imageSort")
                .getTopLevel().getId()).append(")");

        return buff.toString();

    }



}
