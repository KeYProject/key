package org.key_project.jmlediting.core.profile.syntax;

/**
 * This sort specified keywords which can be used at the top level of the parse
 * tree, e.g. a behavior.
 *
 * @author Moritz Lichter
 *
 */
public class ToplevelKeywordSort extends AbstractKeywordSort {

   /**
    * Instance for access.
    */
   public static final ToplevelKeywordSort INSTANCE = new ToplevelKeywordSort();

   /**
    * Only one private instance of this sort.
    */
   private ToplevelKeywordSort() {
      super("Toplevel Keyword");
   }

   /**
    * Used to define subsort of {@link ToplevelKeywordSort} with a new
    * description.
    *
    * @param description
    *           the new description
    */
   protected ToplevelKeywordSort(final String description) {
      super(description);
   }

}
