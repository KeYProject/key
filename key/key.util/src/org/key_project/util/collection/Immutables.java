// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2016 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.util.collection;

import java.util.HashSet;

/**
 * TODO!
 *
 * @author mulbrich
 */
public class Immutables {

    public static <T> boolean isDuplicateFree(ImmutableList<T> list) {

        HashSet<T> set = new HashSet<T>();
        for (T element : list) {
            if(set.contains(element)) {
                return false;
            }
            set.add(element);
        }

        return true;
    }

    public static <T> ImmutableList<T> removeDuplicates(ImmutableList<T> list) {

        if(list.isEmpty()) {
            return list;
        }

        ImmutableList<ImmutableList<T>> stack = ImmutableSLList.nil();

        while(!list.isEmpty()) {
            stack = stack.prepend(list);
            list = list.tail();
        }

        HashSet<T> alreadySeen = new HashSet<T>();
        ImmutableList<T> result = ImmutableSLList.nil();

        while(!stack.isEmpty()) {
            ImmutableList<T> top = stack.head();
            T element = top.head();
            stack = stack.tail();
            if(alreadySeen.contains(element)) {
                // ok, no more reuse possible, go to 2nd loop
                break;
            }
            result = top;
            alreadySeen.add(element);
        }

        while(!stack.isEmpty()) {
            ImmutableList<T> top = stack.head();
            T element = top.head();
            stack = stack.tail();
            if(!alreadySeen.contains(element)) {
                result = result.prepend(element);
                alreadySeen.add(element);
            }
        }

        return result;

    }

}
