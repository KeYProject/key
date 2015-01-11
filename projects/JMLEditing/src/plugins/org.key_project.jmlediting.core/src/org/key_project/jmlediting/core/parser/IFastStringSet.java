package org.key_project.jmlediting.core.parser;

/**
 * The {@link IFastStringSet} is a set of strings which allows fast check,
 * whether a string is contains in the set. The sets requires that for each
 * start character and each string length the number of strings in the set with
 * this start character and length is very small.
 *
 * @author Moritz Lichter
 *
 */
public interface IFastStringSet {

   /**
    * Checks whether the given string is in the set.
    * 
    * @param s
    *           the string to check for
    * @return true, if the string is in the set, false otherwise
    */
   boolean contains(String s);

}
