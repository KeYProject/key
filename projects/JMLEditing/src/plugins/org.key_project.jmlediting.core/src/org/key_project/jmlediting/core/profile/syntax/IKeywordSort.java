package org.key_project.jmlediting.core.profile.syntax;

/**
 * The {@link IKeywordSort} defines the sort of a keyword, for example
 * ToplevelSort or QuantifierSort. Each non abstract implementing class is
 * forces to have a public static final field named INSTANCE which contains the
 * single object created by this sort class.
 *
 * @author Moritz Lichter
 *
 */
public interface IKeywordSort {

   /**
    * Returns a human readable and understandable description of the sort. It
    * can be presented to the user.
    *
    * @return the sort description
    */
   String getDescription();

   /**
    * Checks whether this sort covers the given one. A sort covers another one
    * if both are equal or the class of this sort is a superclass of the other
    * sort.
    *
    * @param other
    *           the sort to check against
    * @return whether this sort covers the other
    */
   boolean covers(IKeywordSort other);

}
