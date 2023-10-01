/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.util;

/**
 * implements a simple object numbering. Each object is assigne a unique long number, which can be
 * used, e.g. for dumping object graphs.
 *
 * @author RN
 */
public class ObjectIDAssignment {

    private static final Index ids = new Index(HashCode.IDENTITY);
    private static long currentId = 0;

    /**
     * retrieves the long id of the given object. If there is currently no such, a new one is
     * automatically created.
     *
     * @param o the object to retrieve an id for
     * @return the unique number of that object
     */
    public static long getID(Object o) {
        long res = ids.get(o);
        if (res == -1L) {
            res = currentId++;
            ids.put(o, res);
        }
        return res;
    }

    /**
     * tells the assignment manager to forget about the given object. CAUTION: The next call to
     * <tt>getID</tt> for the given object will produce a <b>new </b> id.
     *
     * @param the object that is not needed anymore.
     */
    public static void releaseID(Object o) {
        ids.remove(o);
    }

}
